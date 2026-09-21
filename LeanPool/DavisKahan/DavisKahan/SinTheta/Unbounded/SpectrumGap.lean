/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.GapResolvent
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.Gauge
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Spectrum Gap -/

open TauCeti.DavisKahan.Sylvester

/-!
# `sin Θ` endpoints from a spectrum gap

The resolvent construction lives in `DavisKahan.SpectralTheory.GapResolvent`;
these are the two `sin Θ` endpoints it feeds, in operator norm and in an
arbitrary unitarily invariant ideal gauge.  Both are Spectra-free since
2026-07-28 — the gap resolvent is now built from
`TauCeti.LinearPMap.exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap`.
-/

namespace TauCeti
namespace DavisKahan

section SinTheta

open TauCeti.DavisKahan.ExactSinTheta

universe v

variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **The unbounded Davis--Kahan `sin Θ` theorem with genuine spectra.**  For
the paper-shaped unbounded data, if the quadratic form of the trial block
`A₀` lies in `[β, α]` and the resolvent-set spectrum of the complementary
block `Λ₁` avoids the open interval `(β - δ, α + δ)`, then
`δ ‖X⋆ ∘ F₁‖ ≤ ‖R⋆ ∘ F₁‖`.  The resolvent hypothesis of
`sinTheta_unbounded_opNorm` is discharged by the unbounded spectral theorem.
That theorem came from the vendored Spectra package, retired on 2026-07-29. -/
theorem sinTheta_unbounded_opNorm_of_spectrum_gap
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A) (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : TauCeti.LinearPMap.SemiboundedBelow D.A₀ β) (hA₀high : TauCeti.LinearPMap.SemiboundedAbove D.A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum D.Λ₁) :
    δ * ‖D.X.adjoint ∘L D.F₁‖ ≤ ‖D.residual.adjoint ∘L D.F₁‖ := by
  have hΛsa : IsSelfAdjoint D.Λ₁ :=
    LinearPMap.isSelfAdjoint_def.mpr
      (LinearPMap.isSelfAdjoint_def.mp hΛ₁)
  refine sinTheta_unbounded_opNorm D hA hA₀ hΛ₁ hβα hδ hA₀low hA₀high ?_
  refine twoSidedShiftedInverseBound_of_spectrum_gap hΛsa (by linarith) ?_
  intro lam hlam
  refine hΛspec lam ?_
  rw [Set.mem_Ioo] at hlam ⊢
  exact ⟨by linarith [hlam.1], by linarith [hlam.2]⟩

/-- **The unbounded Davis--Kahan `sin Θ` theorem at unitary-invariant ideal
scope, with genuine spectra.**  Combines the ideal-gauge endpoint
`sinTheta_unbounded_gauge` with the spectral-theorem discharge of the
resolvent hypothesis: the only spectral inputs are the trial block's form
bounds and Spectra resolvent-set spectrum avoidance for the complementary
block. -/
theorem sinTheta_unbounded_gauge_of_spectrum_gap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A) (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : TauCeti.LinearPMap.SemiboundedBelow D.A₀ β) (hA₀high : TauCeti.LinearPMap.SemiboundedAbove D.A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum D.Λ₁)
    (hC : N.Mem (D.residual.adjoint ∘L D.F₁)) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gaugeReal (D.X.adjoint ∘L D.F₁) ≤
        N.gaugeReal (D.residual.adjoint ∘L D.F₁) := by
  have hΛsa : IsSelfAdjoint D.Λ₁ :=
    LinearPMap.isSelfAdjoint_def.mpr
      (LinearPMap.isSelfAdjoint_def.mp hΛ₁)
  refine sinTheta_unbounded_gauge N D hA hA₀ hΛ₁ hβα hδ hA₀low hA₀high
    ?_ hC
  refine twoSidedShiftedInverseBound_of_spectrum_gap hΛsa (by linarith) ?_
  intro lam hlam
  refine hΛspec lam ?_
  rw [Set.mem_Ioo] at hlam ⊢
  exact ⟨by linarith [hlam.1], by linarith [hlam.2]⟩

end SinTheta


end DavisKahan
end TauCeti
