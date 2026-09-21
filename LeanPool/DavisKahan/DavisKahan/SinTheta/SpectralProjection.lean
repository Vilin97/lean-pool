/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralRestrictionLocalization
import LeanPool.DavisKahan.DavisKahan.SinTheta.BoundedPerturbation
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.IntervalExterior
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Gap
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Spectral Projection -/

open TauCeti.DavisKahan.Sylvester

/-!
# Canonical unbounded spectral-projection sine-theta theorems

This module converts the complementary overlap block produced by the
unbounded Sylvester argument into the conventional directed gap between two
spectral subspaces.  It then proves the reverse directed estimate directly,
using `A + V` as the base operator and `-V` as the bounded perturbation, and
combines the two estimates with the sharp two-projection norm identity.

No new unbounded analysis occurs here.  The inputs are the Stone spectral
restrictions and localization results from the preceding bridge modules.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahan.ExactSinTheta

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The overlap block between the coordinate inclusions of two complemented
subspaces has the same norm as the corresponding ambient projection product. -/
theorem norm_adjoint_subtypeL_comp_subtypeL_eq
    (U W : Submodule ℂ H)
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    [CompleteSpace U] :
    ‖U.subtypeL.adjoint ∘L W.subtypeL‖ =
      ‖U.starProjection ∘L W.starProjection‖ := by
  rw [Submodule.adjoint_subtypeL]
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _) fun x => ?_
    have hkey :
        ((U.orthogonalProjectionOnto (x : H) : U) : H) =
          (U.starProjection ∘L W.starProjection) (x : H) := by
      change U.starProjection (x : H) =
        U.starProjection (W.starProjection (x : H))
      rw [Submodule.starProjection_eq_self_iff.mpr x.property]
    change ‖((U.orthogonalProjectionOnto (x : H) : U) : H)‖ ≤
      ‖U.starProjection ∘L W.starProjection‖ * ‖(x : H)‖
    rw [hkey]
    exact (U.starProjection ∘L W.starProjection).le_opNorm _
  · refine ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _) fun y => ?_
    have hkey :
        (U.starProjection ∘L W.starProjection) y =
          (((U.orthogonalProjectionOnto ∘L W.subtypeL)
            (W.orthogonalProjectionOnto y) : U) : H) := rfl
    rw [hkey]
    calc
      ‖(((U.orthogonalProjectionOnto ∘L W.subtypeL)
          (W.orthogonalProjectionOnto y) : U) : H)‖
          ≤ ‖U.orthogonalProjectionOnto ∘L W.subtypeL‖ *
              ‖W.orthogonalProjectionOnto y‖ :=
            (U.orthogonalProjectionOnto ∘L W.subtypeL).le_opNorm _
      _ ≤ ‖U.orthogonalProjectionOnto ∘L W.subtypeL‖ * ‖y‖ := by
        refine mul_le_mul_of_nonneg_left ?_
          (ContinuousLinearMap.opNorm_nonneg _)
        change ‖((W.orthogonalProjectionOnto y : W) : H)‖ ≤ ‖y‖
        exact W.norm_starProjection_apply_le y

/-- For spectral ranges, the complementary overlap block is exactly the
standard directed projection gap. -/
theorem norm_spectralComplementaryOverlap_eq_directedGap
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (C : H →ₗ.[ℂ] H) (hC : IsSelfAdjoint C)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S) :
    ‖(selfAdjointSpectralSubspaceInclusion A hA B hB).adjoint ∘L
        selfAdjointSpectralSubspaceInclusion C hC Sᶜ hS.compl‖ =
      Submodule.directedProjectionGap
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace C hC S hS) := by
  let U := selfAdjointSpectralSubspace A hA B hB
  let W := selfAdjointSpectralSubspace C hC S hS
  let Wc := selfAdjointSpectralSubspace C hC Sᶜ hS.compl
  change ‖U.subtypeL.adjoint ∘L Wc.subtypeL‖ =
    ‖Wᗮ.starProjection ∘L U.starProjection‖
  rw [norm_adjoint_subtypeL_comp_subtypeL_eq U Wc]
  have hWc : Wc.starProjection = Wᗮ.starProjection := by
    rw [← selfAdjointSpectralProjection_eq_starProjection C hC Sᶜ hS.compl,
      show selfAdjointSpectralProjection C hC Sᶜ hS.compl
          = ContinuousLinearMap.id ℂ H -
            selfAdjointSpectralProjection C hC S hS from
        (TauCeti.LinearPMap.spectralPVM hC).proj_compl S hS]
    change ContinuousLinearMap.id ℂ H -
        selfAdjointSpectralProjection C hC S hS =
      Wᗮ.starProjection
    rw [selfAdjointSpectralProjection_eq_starProjection C hC S hS]
    exact (Submodule.starProjection_orthogonal' W).symm
  rw [hWc]
  calc
    ‖U.starProjection ∘L Wᗮ.starProjection‖ =
        ‖(U.starProjection ∘L Wᗮ.starProjection).adjoint‖ := by
      symm
      exact ContinuousLinearMap.adjoint.norm_map _
    _ = ‖Wᗮ.starProjection ∘L U.starProjection‖ := by
      rw [ContinuousLinearMap.adjoint_comp,
        ← ContinuousLinearMap.star_eq_adjoint,
        ← ContinuousLinearMap.star_eq_adjoint,
        (isSelfAdjoint_starProjection Wᗮ).star_eq,
        (isSelfAdjoint_starProjection U).star_eq]

/-- Directed unbounded Davis--Kahan theorem for genuine spectral subspaces,
stated with the spectral bounds of the two canonical restricted operators. -/
theorem sinTheta_addBounded_directedGap_of_spectrum_gap
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hScomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction (TauCeti.LinearPMap.addBounded A V)
          (addBounded_isSelfAdjoint A hA V hV) Sᶜ hS.compl)) :
    δ * Submodule.directedProjectionGap
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A V)
          (addBounded_isSelfAdjoint A hA V hV) S hS) ≤ ‖V‖ := by
  have hraw :=
    sinTheta_addBounded_spectralSubspaces_opNorm_of_spectrum_gap
      A hA V hV B Sᶜ hB hS.compl hβα hδ hBlow hBhigh hScomplSpec
  rw [norm_spectralComplementaryOverlap_eq_directedGap
    A hA (TauCeti.LinearPMap.addBounded A V) (addBounded_isSelfAdjoint A hA V hV)
    B S hB hS] at hraw
  exact hraw

/-- Set-localized one-sided specialization.  This remains useful when the
selected perturbed set contains a full neighborhood of the exact cluster. -/
theorem sinTheta_addBounded_directedGap_of_intervalExterior
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hScomplDisj : Sᶜ ∩ Set.Ioo (β - δ) (α + δ) = ∅) :
    δ * Submodule.directedProjectionGap
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A V)
          (addBounded_isSelfAdjoint A hA V hV) S hS) ≤ ‖V‖ := by
  obtain ⟨hBlow, hBhigh⟩ :=
    selfAdjointSpectralRestriction_semibounded_of_subset_Icc
      A hA B hB hBsub
  have hScomplSpec :=
    selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      (TauCeti.LinearPMap.addBounded A V) (addBounded_isSelfAdjoint A hA V hV)
      Sᶜ hS.compl hScomplDisj
  exact sinTheta_addBounded_directedGap_of_spectrum_gap
    A hA V hV B S hB hS hβα hδ hBlow hBhigh hScomplSpec

/-- Reverse directed estimate.  This is proved without replacing
`(A + V) + (-V)` by `A` as a bundled closed operator: the original spectral
restriction is supplied directly as the unwanted complementary block, and
its intertwining equation follows by cancellation of `V` and `-V`. -/
theorem sinTheta_addBounded_reverseDirectedGap_of_spectrum_gap
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hSlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction (TauCeti.LinearPMap.addBounded A V)
        (addBounded_isSelfAdjoint A hA V hV) S hS) β)
    (hShigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction (TauCeti.LinearPMap.addBounded A V)
        (addBounded_isSelfAdjoint A hA V hV) S hS) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl)) :
    δ * Submodule.directedProjectionGap
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A V)
          (addBounded_isSelfAdjoint A hA V hV) S hS)
        (selfAdjointSpectralSubspace A hA B hB) ≤ ‖V‖ := by
  let C := TauCeti.LinearPMap.addBounded A V
  let hC : IsSelfAdjoint C := addBounded_isSelfAdjoint A hA V hV
  have hnegV : (-V).IsSymmetric := by
    intro x y
    change ⟪-V x, y⟫_ℂ = ⟪x, -V y⟫_ℂ
    simpa using congrArg Neg.neg (hV x y)
  let X := selfAdjointSpectralSubspaceInclusion C hC S hS
  let F₁ := selfAdjointSpectralSubspaceInclusion A hA Bᶜ hB.compl
  let A₀ := selfAdjointSpectralRestriction C hC S hS
  let Λ₁ := selfAdjointSpectralRestriction A hA Bᶜ hB.compl
  have hXdom : ∀ x : A₀.domain, X (x : _) ∈ C.domain :=
    selfAdjointSpectralRestriction_inclusion_mem_domain C hC S hS
  have hXint : ∀ x : A₀.domain,
      C ⟨X (x : _), hXdom x⟩ = X (A₀ x) :=
    selfAdjointSpectralRestriction_inclusion_intertwines C hC S hS
  have hFdom : ∀ y : Λ₁.domain, F₁ (y : _) ∈ C.domain := by
    intro y
    exact selfAdjointSpectralRestriction_inclusion_mem_domain
      A hA Bᶜ hB.compl y
  have hFint : ∀ y : Λ₁.domain,
      (TauCeti.LinearPMap.addBounded C (-V)) ⟨F₁ (y : _), hFdom y⟩ =
        F₁ (Λ₁ y) := by
    intro y
    have hAint := selfAdjointSpectralRestriction_inclusion_intertwines
      A hA Bᶜ hB.compl y
    change
      (A ⟨F₁ (y : _), hFdom y⟩ + V (F₁ (y : _))) +
          (-V) (F₁ (y : _)) =
        F₁ (Λ₁ y)
    simpa only [neg_apply, add_neg_cancel_right] using hAint
  have hraw := sinTheta_addBounded_opNorm_of_spectrum_gap_isometric
    C hC (-V) hnegV A₀
    (selfAdjointSpectralRestriction_isSelfAdjoint C hC S hS)
    Λ₁ (selfAdjointSpectralRestriction_isSelfAdjoint A hA Bᶜ hB.compl)
    X F₁ hXdom hXint hFdom hFint
    (selfAdjointSpectralSubspaceInclusion_isometric C hC S hS)
    (selfAdjointSpectralSubspaceInclusion_isometric A hA Bᶜ hB.compl)
    hβα hδ hSlow hShigh hBcomplSpec
  change δ * ‖(selfAdjointSpectralSubspaceInclusion C hC S hS).adjoint ∘L
      selfAdjointSpectralSubspaceInclusion A hA Bᶜ hB.compl‖ ≤ ‖-V‖ at hraw
  rw [norm_spectralComplementaryOverlap_eq_directedGap
    C hC A hA S B hS hB, norm_neg] at hraw
  exact hraw

/-- Symmetric conventional unbounded Davis--Kahan `sin Θ` theorem, stated
with semibounds and resolvent gaps for the four canonical spectral
restrictions. -/
theorem sinTheta_addBounded_spectralProjection_sub_opNorm_of_formBounds
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α β' α' δ : ℝ}
    (hβα : β ≤ α) (hβ'α' : β' ≤ α') (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hScomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction (TauCeti.LinearPMap.addBounded A V)
          (addBounded_isSelfAdjoint A hA V hV) Sᶜ hS.compl))
    (hSlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction (TauCeti.LinearPMap.addBounded A V)
        (addBounded_isSelfAdjoint A hA V hV) S hS) β')
    (hShigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction (TauCeti.LinearPMap.addBounded A V)
        (addBounded_isSelfAdjoint A hA V hV) S hS) α')
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β' - δ) (α' + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl)) :
    δ * ‖selfAdjointSpectralProjection A hA B hB -
      selfAdjointSpectralProjection (TauCeti.LinearPMap.addBounded A V)
        (addBounded_isSelfAdjoint A hA V hV) S hS‖ ≤ ‖V‖ := by
  let U := selfAdjointSpectralSubspace A hA B hB
  let W := selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A V)
    (addBounded_isSelfAdjoint A hA V hV) S hS
  have hforward : δ * U.directedProjectionGap W ≤ ‖V‖ :=
    sinTheta_addBounded_directedGap_of_spectrum_gap
      A hA V hV B S hB hS hβα hδ hBlow hBhigh hScomplSpec
  have hreverse : δ * W.directedProjectionGap U ≤ ‖V‖ :=
    sinTheta_addBounded_reverseDirectedGap_of_spectrum_gap
      A hA V hV B S hB hS hβ'α' hδ hSlow hShigh hBcomplSpec
  have hmax : U.projectionGap W =
      max (U.directedProjectionGap W) (W.directedProjectionGap U) := by
    change ‖U.starProjection - W.starProjection‖ =
      max ‖Wᗮ.starProjection ∘L U.starProjection‖
        ‖Uᗮ.starProjection ∘L W.starProjection‖
    rw [Submodule.norm_starProjection_sub_eq_max,
      Submodule.starProjection_orthogonal' W,
      Submodule.starProjection_orthogonal' U]
  rw [selfAdjointSpectralProjection_eq_starProjection A hA B hB,
    selfAdjointSpectralProjection_eq_starProjection (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) S hS]
  change δ * U.projectionGap W ≤ ‖V‖
  rw [hmax, mul_max_of_nonneg _ _ hδ.le]
  exact max_le hforward hreverse

/-- Genuine-spectrum form of the canonical unbounded spectral-projection
`sin Θ` theorem.  The interval hypotheses are imposed on the actual spectra
of the selected Stone restrictions, rather than on the raw Borel sets. -/
theorem sinTheta_addBounded_spectralProjection_sub_opNorm_of_spectrum_gap
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α β' α' δ : ℝ}
    (hβα : β ≤ α) (hβ'α' : β' ≤ α') (hδ : 0 < δ)
    (hBspec : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum
      (selfAdjointSpectralRestriction A hA B hB) ⊆
        Set.Icc β α)
    (hScomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction (TauCeti.LinearPMap.addBounded A V)
          (addBounded_isSelfAdjoint A hA V hV) Sᶜ hS.compl))
    (hSspec : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum
      (selfAdjointSpectralRestriction (TauCeti.LinearPMap.addBounded A V)
        (addBounded_isSelfAdjoint A hA V hV) S hS) ⊆
        Set.Icc β' α')
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β' - δ) (α' + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl)) :
    δ * ‖selfAdjointSpectralProjection A hA B hB -
      selfAdjointSpectralProjection (TauCeti.LinearPMap.addBounded A V)
        (addBounded_isSelfAdjoint A hA V hV) S hS‖ ≤ ‖V‖ := by
  obtain ⟨hBlow, hBhigh⟩ := semibounded_of_spectrum_subset_Icc
    (selfAdjointSpectralRestriction_isSelfAdjoint A hA B hB) hβα hBspec
  obtain ⟨hSlow, hShigh⟩ := semibounded_of_spectrum_subset_Icc
    (selfAdjointSpectralRestriction_isSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) S hS) hβ'α' hSspec
  exact sinTheta_addBounded_spectralProjection_sub_opNorm_of_formBounds
    A hA V hV B S hB hS hβα hβ'α' hδ
    hBlow hBhigh hScomplSpec hSlow hShigh hBcomplSpec

end DavisKahan
end TauCeti
