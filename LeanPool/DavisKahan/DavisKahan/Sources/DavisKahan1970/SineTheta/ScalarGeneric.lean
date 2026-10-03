/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.BoundedPerturbation
public import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarGeneric
public import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.FormBoundedGap
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm

/-! # Scalar Generic -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Scalar-generic headline `sin Theta` theorem

This module gives the Section 2 single-angle sine theorem an intentionally
paper-facing production surface.  The analytic engine is scalar-generic through
`HasUnboundedSylvesterKyFan` and
`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`, both of which hold at every
`RCLike` field: `TauCeti.DavisKahan.Sylvester.hasUnboundedSylvesterKyFan` and
`ContinuousLinearMap.hasMinMaxLowerBoundEverywhere` obtain them by transporting
the fixed-field proofs along the real/complex dichotomy of `RCLike`.  They are
therefore implementation infrastructure, resolved by instance search, and no
theorem in this module quantifies over them.

The public theorem `sinTheta_unbounded_intervalExterior_symmetricNorming_rclike` avoids the
  historical bundled
problem records.  It displays the operators, coordinate maps, residual
identity, exact-space decomposition, interval/exterior spectral separation,
and universal source unitary-invariant norm directly in its type.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace

noncomputable section

universe u v

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

section GenericEngine

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Scalar-generic exact unbounded `sin Theta` endpoint at the canonical
Ky-Fan-dominant ideal-family layer.  This is the reusable engine behind the
paper-facing theorem below. -/
theorem sinTheta_unbounded_formGap_idealFamily_rclike
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (F₀ : H →L[𝕜] E)
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
        ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.gauge
          ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L D.X)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le
    N.toSymmetricOperatorIdealFamily D hdecomp.isometry₁ hR
  have hRaw :
      N.Mem (D.X.adjoint ∘L D.F₁) ∧
        δ * N.gauge (D.X.adjoint ∘L D.F₁) ≤
          N.gauge (-(D.residual.adjoint ∘L D.F₁)) := by
    apply mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hδ hC.1
    intro k
    exact unbounded_sylvester_kyFan hA₀ hΛ₁ hδ hgap hEq k
  have hC' :
      N.gauge (-(D.residual.adjoint ∘L D.F₁)) ≤ N.gauge D.residual := by
    simpa only [FanDominantIdealFamily.toSymmetric_gaugeReal] using hC.2
  have hBlock :
      N.Mem (D.X.adjoint ∘L D.F₁) ∧
        δ * N.gauge (D.X.adjoint ∘L D.F₁) ≤ N.gauge D.residual :=
    ⟨hRaw.1, hRaw.2.trans hC'⟩
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N.toSymmetricOperatorIdealFamily D.X F₀ D.F₁ hX hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [FanDominantIdealFamily.toSymmetric_gaugeReal] at hAngle
  rw [hAngle.2]
  exact hBlock.2

/-- Scalar-generic complementary-block form of the unbounded `sin Theta` estimate.

Unlike `sinTheta_unbounded_formGap_idealFamily_rclike`, this stops before converting the
rectangular Sylvester block into the ambient directed sine.  The double-angle reflection
argument needs exactly this sharper intermediate form. -/
theorem sinTheta_unbounded_formGap_idealFamily_block_rclike
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hF₁ : IsometricEmbedding D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁) ≤
        N.gauge (D.residual.adjoint ∘L D.F₁) := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le
    N.toSymmetricOperatorIdealFamily D hF₁ hR
  have hRaw :
      N.Mem (D.X.adjoint ∘L D.F₁) ∧
        δ * N.gauge (D.X.adjoint ∘L D.F₁) ≤
          N.gauge (-(D.residual.adjoint ∘L D.F₁)) := by
    apply mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
      N.toFanDominantIdealFamily hδ hC.1
    intro k
    exact unbounded_sylvester_kyFan hA₀ hΛ₁ hδ hgap hEq k
  have hmem : N.Mem (D.residual.adjoint ∘L D.F₁) :=
    N.toSymmetricOperatorIdealFamily.comp_right_mem D.F₁
      (N.toSymmetricOperatorIdealFamily.adjoint_mem hR)
  refine ⟨hRaw.1, hRaw.2.trans (le_of_eq ?_)⟩
  exact N.toSymmetricOperatorIdealFamily.gaugeReal_neg hmem

/-- Scalar-generic bounded-perturbation block adapter at the full form-bounded gap.

This is the common real/complex engine formerly duplicated by
`sinTheta_addBounded_gauge_complex_block_of_formGap` and
`sinTheta_addBounded_gauge_real_block`. -/
theorem sinTheta_addBounded_gauge_block_of_formGap_rclike
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    (A : E →ₗ.[𝕜] E) (hA : IsSelfAdjoint A)
    (Vop : E →L[𝕜] E) (hVop : Vop.IsSymmetric)
    (A₀ : F →ₗ.[𝕜] F) (hA₀ : IsSelfAdjoint A₀)
    (Λ₁ : G →ₗ.[𝕜] G) (hΛ₁ : IsSelfAdjoint Λ₁)
    (X : F →L[𝕜] E) (F₁ : G →L[𝕜] E)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A ⟨X (x : F), hXdom x⟩ = X (A₀ x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (TauCeti.LinearPMap.addBounded A Vop) ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁ y))
    (hF₁iso : IsometricEmbedding F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hVmem : N.Mem Vop) :
    N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gauge (X.adjoint ∘L F₁) ≤
        N.gauge ((Vop ∘L X).adjoint ∘L F₁) := by
  let D := boundedPerturbationSinThetaData A Vop A₀ Λ₁ X F₁
    hXdom hXintertwines hF₁dom hF₁intertwines
  have hD : _root_.IsSelfAdjoint D.A := by
    change _root_.IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Vop)
    exact addBounded_isSelfAdjoint A hA Vop hVop
  have hResMem : N.Mem D.residual := by
    change N.Mem (Vop ∘L X)
    exact N.toSymmetricOperatorIdealFamily.comp_right_mem X hVmem
  exact sinTheta_unbounded_formGap_idealFamily_block_rclike
    N D hD hA₀ hΛ₁ hF₁iso hδ hgap hResMem

/-- **Davis--Kahan 1970, Section 2 `sin Theta` theorem, scalar-generic
paper-facing form, at the full source gap.**

This is the Section 2 sine theorem at the printed scope and generic over the
scalar field: an unbounded self-adjoint ambient operator, a separable Hilbert
space of arbitrary dimension, an arbitrary source unitarily invariant norm, and
both printed conclusions -- membership of the sine block in the norm's ideal and
the factor-one inequality.

`hgap` is the whole `FormBoundedSylvesterGap`, not one of its branches.  That
matters for source fidelity rather than for generality alone: the printed
theorem separates the spectra by an interval and its exterior, and the source
also permits those intervals to be half-infinite, which is what the two
semibounded constructors carry.  `sinTheta_unbounded_intervalExterior_symmetricNorming_rclike`
  below is this theorem
with the bounded-interval branch spelled out, and
`DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike` is it again with the
structural hypotheses bundled as `IsTrialResidual` and `IsExactSpectralDecomposition`.

`[RCLike 𝕜]` is the whole scalar hypothesis.  This theorem carried two capability
binders until 2026-09-03; both classes have unconditional instances at every
`RCLike` field, so they were never hypotheses of the mathematics and instance
search supplies them. -/
theorem sinTheta_unbounded_formGap_symmetricNorming_ofComponents_rclike
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E)
    (F₀ : H →L[𝕜] E)
    (F₁ : G →L[𝕜] E)
    (R : F →L[𝕜] E)
    (hA : IsSelfAdjoint A)
    (hA₀ : IsSelfAdjoint A₀)
    (hΛ₁ : IsSelfAdjoint Λ₁)
    (hE₀ : IsometricEmbedding E₀)
    (hF₀ : IsometricEmbedding F₀)
    (hF₁ : IsometricEmbedding F₁)
    (horth : F₀.adjoint ∘L F₁ = 0)
    (hdecomp :
      F₀ ∘L F₀.adjoint + F₁ ∘L F₁.adjoint = ContinuousLinearMap.id 𝕜 E)
    (hE₀dom : ∀ x : A₀.domain, E₀ (x : F) ∈ A.domain)
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hresidual : ∀ x : A₀.domain,
      A ⟨E₀ (x : F), hE₀dom x⟩ - E₀ (A₀ x) = R (x : F))
    (hintertwines : ∀ y : Λ₁.domain,
      A ⟨F₁ (y : G), hF₁dom y⟩ = F₁ (Λ₁ y))
    {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R := by
  let D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G) :=
    { A := A
      A₀ := A₀
      Λ₁ := Λ₁
      X := E₀
      F₁ := F₁
      residual := R
      X_maps_domain := hE₀dom
      F₁_maps_domain := hF₁dom
      residual_eq := hresidual
      intertwines := hintertwines }
  have hExact : OrthogonalExactDecomposition F₀ F₁ :=
    { isometry₀ := hF₀
      isometry₁ := hF₁
      orthogonal := horth
      projection_sum := hdecomp }
  apply N.mul_gauge_le_of_all_mul_kyFan_le hδ hR
  intro k
  by_cases hk : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hmain := sinTheta_unbounded_formGap_idealFamily_rclike
      (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hkpos)
      D F₀ hA hA₀ hΛ₁ hE₀ hExact hδ hgap
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := 𝕜) k hkpos R)
    simpa only [D, KyFanDominantIdealFamily.kyFan_gauge] using hmain.2

/-- **Davis--Kahan 1970, Section 2 `sin Theta` theorem, scalar-generic
paper-facing form.**

The theorem is stated over an arbitrary `RCLike` scalar field carrying the two
analytic capabilities already proved for both `R` and `C`.  Apart from those
field capabilities, the signature displays the mathematical source data
explicitly instead of hiding it in a local problem structure.

The interval/exterior hypothesis is written literally: one of `A0` and
`Lambda1` has real spectrum in `[beta, alpha]`, while the other avoids the open
`delta`-neighborhood of that interval. -/
theorem sinTheta_unbounded_intervalExterior_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E)
    (F₀ : H →L[𝕜] E)
    (F₁ : G →L[𝕜] E)
    (R : F →L[𝕜] E)
    (hA : IsSelfAdjoint A)
    (hA₀ : IsSelfAdjoint A₀)
    (hΛ₁ : IsSelfAdjoint Λ₁)
    (hE₀ : IsometricEmbedding E₀)
    (hF₀ : IsometricEmbedding F₀)
    (hF₁ : IsometricEmbedding F₁)
    (horth : F₀.adjoint ∘L F₁ = 0)
    (hdecomp :
      F₀ ∘L F₀.adjoint + F₁ ∘L F₁.adjoint = ContinuousLinearMap.id 𝕜 E)
    (hE₀dom : ∀ x : A₀.domain, E₀ (x : F) ∈ A.domain)
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hresidual : ∀ x : A₀.domain,
      A ⟨E₀ (x : F), hE₀dom x⟩ - E₀ (A₀ x) = R (x : F))
    (hintertwines : ∀ y : Λ₁.domain,
      A ⟨F₁ (y : G), hF₁dom y⟩ = F₁ (Λ₁ y))
    {β α δ : ℝ}
    (hβα : β ≤ α)
    (hδ : 0 < δ)
    (hspectral :
      (TauCeti.LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α ∧
          TauCeti.LinearPMap.realSpectrum Λ₁ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}) ∨
        (TauCeti.LinearPMap.realSpectrum Λ₁ ⊆ Set.Icc β α ∧
          TauCeti.LinearPMap.realSpectrum A₀ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}))
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  sinTheta_unbounded_formGap_symmetricNorming_ofComponents_rclike N A A₀ Λ₁ E₀ F₀ F₁ R
    hA hA₀ hΛ₁ hE₀ hF₀ hF₁ horth hdecomp hE₀dom hF₁dom hresidual hintertwines
    hδ (FormBoundedSylvesterGap.intervalExterior hβα hspectral) hR

end GenericEngine

end

end DavisKahan1970
end TauCeti
