/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralRestrictionLocalization
import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.SpectrumGap
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions

/-! # Bounded Perturbation -/

open TauCeti.DavisKahan.Sylvester

/-!
# Bounded-perturbation adapter for the unbounded sine-theta theorem

This module removes two pieces of provisional plumbing from the route to the
classical unbounded perturbation statement.

First, Spectra's bounded Kato--Rellich theorem proves that `A + V`, on the
original domain of a self-adjoint closed operator `A`, is self-adjoint whenever
`V` is bounded and self-adjoint.

Second, `boundedPerturbationSinThetaData` packages exact and trial spectral
blocks into `UnboundedSinThetaData`.  The residual is automatically `V X`.
The resulting theorem reduces the desired perturbation estimate to construction
of the two spectral restrictions and their intertwining maps; no ideal or
Halmos machinery is used.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahan.ExactSinTheta

universe u v

section ScalarGeneric

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H F G : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

omit [CompleteSpace H] in
/-- The DK bounded sum is exactly the canonical partial-map perturbation.

Was stated over `Spectra.Operator.perturbedOp` until 2026-07-28; the canonical
object is now `TauCeti.LinearPMap.perturb`
(the completed Spectra removal). -/
theorem toLinearPMap_addBounded_eq_perturbedOp
    (A : H →ₗ.[𝕜] H) (V : H →L[𝕜] H) :
    (TauCeti.LinearPMap.addBounded A V) =
      TauCeti.LinearPMap.perturb A
        (TauCeti.LinearPMap.boundedPerturbation A V) := by
  refine LinearPMap.ext_iff.mpr ⟨rfl, ?_⟩
  intro x hx hy
  rfl

/-- Bounded Kato--Rellich: a bounded self-adjoint perturbation of a self-adjoint
partial map is self-adjoint on the same domain. -/
theorem addBounded_isSelfAdjoint
    (A : H →ₗ.[𝕜] H)
    (hA : IsSelfAdjoint A)
    (V : H →L[𝕜] H) (hV : V.IsSymmetric) :
    _root_.IsSelfAdjoint (TauCeti.LinearPMap.addBounded A V) := by
  have hV' : _root_.IsSelfAdjoint V :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hV
  change _root_.IsSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
  rw [toLinearPMap_addBounded_eq_perturbedOp]
  exact TauCeti.LinearPMap.isSelfAdjoint_perturb_bounded hA hV'

/-- Package a bounded perturbation and two invariant block embeddings as the
paper-shaped unbounded residual data.  The residual identity is automatic and
has residual `V ∘ X`. -/
noncomputable def boundedPerturbationSinThetaData
    (A : H →ₗ.[𝕜] H) (V : H →L[𝕜] H)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (X : F →L[𝕜] H) (F₁ : G →L[𝕜] H)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A ⟨X (x : F), hXdom x⟩ = X (A₀ x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (TauCeti.LinearPMap.addBounded A V) ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁ y)) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := H) (F := F) (G := G) where
  A := TauCeti.LinearPMap.addBounded A V
  A₀ := A₀
  Λ₁ := Λ₁
  X := X
  F₁ := F₁
  residual := V ∘L X
  X_maps_domain := hXdom
  F₁_maps_domain := hF₁dom
  residual_eq := by
    intro x
    change
      (A ⟨X (x : F), hXdom x⟩ + V (X (x : F))) -
          X (A₀ x) =
        V (X (x : F))
    rw [hXintertwines x]
    abel
  intertwines := hF₁intertwines

end ScalarGeneric

variable {H F G : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- The projected adjoint residual of a bounded perturbation is no larger than
`V` when both block embeddings are contractions. -/
theorem boundedPerturbation_adjointResidual_opNorm_le
    (V : H →L[ℂ] H) (X : F →L[ℂ] H) (F₁ : G →L[ℂ] H)
    (hX : ‖X‖ ≤ 1) (hF₁ : ‖F₁‖ ≤ 1) :
    ‖(V ∘L X).adjoint ∘L F₁‖ ≤ ‖V‖ := by
  calc
    ‖(V ∘L X).adjoint ∘L F₁‖
        ≤ ‖(V ∘L X).adjoint‖ * ‖F₁‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖V ∘L X‖ * ‖F₁‖ := by
          rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ (‖V‖ * ‖X‖) * ‖F₁‖ :=
          mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ (‖V‖ * 1) * ‖F₁‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hX (norm_nonneg V)) (norm_nonneg F₁)
    _ ≤ (‖V‖ * 1) * 1 :=
          mul_le_mul_of_nonneg_left hF₁
            (mul_nonneg (norm_nonneg V) zero_le_one)
    _ = ‖V‖ := by ring

/-- Bounded-perturbation specialization of the genuine-spectrum unbounded
sine-theta theorem.  The only remaining block-specific inputs are the two
self-adjoint restricted operators, their domain-aware intertwining maps, and
the interval/exterior spectral hypotheses. -/
theorem sinTheta_addBounded_opNorm_of_spectrum_gap
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (A₀ : F →ₗ.[ℂ] F) (hA₀ : IsSelfAdjoint A₀)
    (Λ₁ : G →ₗ.[ℂ] G) (hΛ₁ : IsSelfAdjoint Λ₁)
    (X : F →L[ℂ] H) (F₁ : G →L[ℂ] H)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A ⟨X (x : F), hXdom x⟩ = X (A₀ x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (TauCeti.LinearPMap.addBounded A V) ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁ y))
    (hXnorm : ‖X‖ ≤ 1) (hF₁norm : ‖F₁‖ ≤ 1)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : TauCeti.LinearPMap.SemiboundedBelow A₀ β) (hA₀high :
      TauCeti.LinearPMap.SemiboundedAbove A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum Λ₁) :
    δ * ‖X.adjoint ∘L F₁‖ ≤ ‖V‖ := by
  let D := boundedPerturbationSinThetaData A V A₀ Λ₁ X F₁
    hXdom hXintertwines hF₁dom hF₁intertwines
  have hD : _root_.IsSelfAdjoint D.A := by
    change _root_.IsSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
    exact addBounded_isSelfAdjoint A hA V hV
  have hraw := sinTheta_unbounded_opNorm_of_spectrum_gap D hD hA₀ hΛ₁
    hβα hδ hA₀low hA₀high hΛspec
  have hraw' :
      δ * ‖X.adjoint ∘L F₁‖ ≤ ‖(V ∘L X).adjoint ∘L F₁‖ := by
    change δ * ‖X.adjoint ∘L F₁‖ ≤ ‖(V ∘L X).adjoint ∘L F₁‖ at hraw
    exact hraw
  have hres := boundedPerturbation_adjointResidual_opNorm_le V X F₁
    hXnorm hF₁norm
  exact hraw'.trans hres

/-- Isometric-embedding form of
`sinTheta_addBounded_opNorm_of_spectrum_gap`. -/
theorem sinTheta_addBounded_opNorm_of_spectrum_gap_isometric
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (A₀ : F →ₗ.[ℂ] F) (hA₀ : IsSelfAdjoint A₀)
    (Λ₁ : G →ₗ.[ℂ] G) (hΛ₁ : IsSelfAdjoint Λ₁)
    (X : F →L[ℂ] H) (F₁ : G →L[ℂ] H)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A ⟨X (x : F), hXdom x⟩ = X (A₀ x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (TauCeti.LinearPMap.addBounded A V) ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁ y))
    (hXiso : IsometricEmbedding X) (hF₁iso : IsometricEmbedding F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : TauCeti.LinearPMap.SemiboundedBelow A₀ β) (hA₀high :
      TauCeti.LinearPMap.SemiboundedAbove A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum Λ₁) :
    δ * ‖X.adjoint ∘L F₁‖ ≤ ‖V‖ := by
  exact sinTheta_addBounded_opNorm_of_spectrum_gap A hA V hV
    A₀ hA₀ Λ₁ hΛ₁ X F₁ hXdom hXintertwines hF₁dom hF₁intertwines
    (opNorm_le_one_of_isometry hXiso) (opNorm_le_one_of_isometry hF₁iso)
    hβα hδ hA₀low hA₀high hΛspec


/-- The canonical bounded-perturbation residual data built from the exact and
perturbed spectral-range Stone generators. -/
noncomputable def spectralBoundedPerturbationSinThetaData
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (B T : Set ℝ) (hB : MeasurableSet B) (hT : MeasurableSet T) :
    UnboundedSinThetaData (𝕜 := ℂ) (E := H)
      (F := selfAdjointSpectralSubspace A hA B hB)
      (G := selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A V)
        (addBounded_isSelfAdjoint A hA V hV) T hT) :=
  boundedPerturbationSinThetaData A V
    (selfAdjointSpectralRestriction A hA B hB)
    (selfAdjointSpectralRestriction (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) T hT)
    (selfAdjointSpectralSubspaceInclusion A hA B hB)
    (selfAdjointSpectralSubspaceInclusion (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) T hT)
    (selfAdjointSpectralRestriction_inclusion_mem_domain A hA B hB)
    (selfAdjointSpectralRestriction_inclusion_intertwines A hA B hB)
    (selfAdjointSpectralRestriction_inclusion_mem_domain (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) T hT)
    (selfAdjointSpectralRestriction_inclusion_intertwines (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) T hT)

/-- Genuine spectral-subspace specialization of the unbounded
bounded-perturbation sine-theta estimate.  The remaining hypotheses are now
only spectral localization facts about the two canonical restricted
operators. -/
theorem sinTheta_addBounded_spectralSubspaces_opNorm_of_spectrum_gap
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (B T : Set ℝ) (hB : MeasurableSet B) (hT : MeasurableSet T)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hA₀high : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction (TauCeti.LinearPMap.addBounded A V)
          (addBounded_isSelfAdjoint A hA V hV) T hT)) :
    δ * ‖(selfAdjointSpectralSubspaceInclusion A hA B hB).adjoint ∘L
      selfAdjointSpectralSubspaceInclusion (TauCeti.LinearPMap.addBounded A V)
        (addBounded_isSelfAdjoint A hA V hV) T hT‖ ≤ ‖V‖ := by
  exact sinTheta_addBounded_opNorm_of_spectrum_gap_isometric A hA V hV
    (selfAdjointSpectralRestriction A hA B hB)
    (selfAdjointSpectralRestriction_isSelfAdjoint A hA B hB)
    (selfAdjointSpectralRestriction (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) T hT)
    (selfAdjointSpectralRestriction_isSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) T hT)
    (selfAdjointSpectralSubspaceInclusion A hA B hB)
    (selfAdjointSpectralSubspaceInclusion (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) T hT)
    (selfAdjointSpectralRestriction_inclusion_mem_domain A hA B hB)
    (selfAdjointSpectralRestriction_inclusion_intertwines A hA B hB)
    (selfAdjointSpectralRestriction_inclusion_mem_domain (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) T hT)
    (selfAdjointSpectralRestriction_inclusion_intertwines (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) T hT)
    (selfAdjointSpectralSubspaceInclusion_isometric A hA B hB)
    (selfAdjointSpectralSubspaceInclusion_isometric (TauCeti.LinearPMap.addBounded A V)
      (addBounded_isSelfAdjoint A hA V hV) T hT)
    hβα hδ hA₀low hA₀high hΛspec


/-- Canonical interval/exterior bounded-perturbation sine-theta theorem.
The interval and exterior hypotheses are stated directly on the measurable
spectral sets selecting the exact and perturbed subspaces; the spectral
localization of their Stone generators is discharged internally. -/
theorem sinTheta_addBounded_spectralSubspaces_opNorm_of_intervalExterior
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (B T : Set ℝ) (hB : MeasurableSet B) (hT : MeasurableSet T)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hTdisj : T ∩ Set.Ioo (β - δ) (α + δ) = ∅) :
    δ * ‖(selfAdjointSpectralSubspaceInclusion A hA B hB).adjoint ∘L
      selfAdjointSpectralSubspaceInclusion (TauCeti.LinearPMap.addBounded A V)
        (addBounded_isSelfAdjoint A hA V hV) T hT‖ ≤ ‖V‖ := by
  obtain ⟨hA₀low, hA₀high⟩ :=
    selfAdjointSpectralRestriction_semibounded_of_subset_Icc
      A hA B hB hBsub
  have hΛspec :=
    selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      (TauCeti.LinearPMap.addBounded A V) (addBounded_isSelfAdjoint A hA V hV)
      T hT hTdisj
  exact sinTheta_addBounded_spectralSubspaces_opNorm_of_spectrum_gap
    A hA V hV B T hB hT hβα hδ hA₀low hA₀high hΛspec

end DavisKahan
end TauCeti
