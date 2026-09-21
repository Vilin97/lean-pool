/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import LeanPool.PoincareGeometry.LichnerowiczObata.LocalIntegralCurveUniqueness

/-! # Identifying normal coordinate rays with radial integral curves -/

@[expose] public noncomputable section
open Set
open scoped Manifold ContDiff
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A radial derivative identity for a parameter map gives the integral
curve equation along each scaled ray. The scalar is cancelled only where
it is nonzero. -/
theorem isMIntegralCurveOn_normal_ray
    (ψ : P → M) (u : P) (V : (x : M) → TangentSpace I x) (J : Set ℝ)
    (hne : ∀ r ∈ J, r ≠ 0)
    (hψ : ∀ r ∈ J, MDifferentiableAt 𝓘(ℝ, P) I ψ (r • u))
    (hrad : ∀ r ∈ J, mfderiv 𝓘(ℝ, P) I ψ (r • u) (r • u) =
      r • V (ψ (r • u))) :
    IsMIntegralCurveOn (fun r => ψ (r • u)) V J := by
  intro r hr
  have hdu : mfderiv 𝓘(ℝ, P) I ψ (r • u) u = V (ψ (r • u)) := by
    apply smul_right_injective (TangentSpace I (ψ (r • u))) (hne r hr)
    simpa only [map_smul] using hrad r hr
  let A : ℝ →L[ℝ] P := (1 : ℝ →L[ℝ] ℝ).smulRight u
  have hA : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, P) A r A :=
    hasMFDerivAt_iff_hasFDerivAt.mpr A.hasFDerivAt
  have hc := (hψ r hr).hasMFDerivAt.comp r hA
  have he : (mfderiv 𝓘(ℝ, P) I ψ (r • u)).comp A =
      (1 : ℝ →L[ℝ] ℝ).smulRight (V (ψ (r • u))) := by
    apply ContinuousLinearMap.ext
    intro s
    change mfderiv 𝓘(ℝ, P) I ψ (r • u) (s • u) = s • V (ψ (r • u))
    rw [map_smul, hdu]
  rw [he] at hc
  exact hc.hasMFDerivWithinAt

/-- On a positive interval, a normal ray and an integral curve with one
common point agree everywhere on that interval. This identifies the maps,
not just their radial levels or tangent norms. -/
theorem normal_ray_eq_integralCurve [CompleteSpace E] [IsManifold I 1 M]
    [I.Boundaryless] [T2Space M]
    (ψ : P → M) (u : P) (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    {a b r₀ : ℝ} (ha : 0 ≤ a) (hr₀ : r₀ ∈ Ioo a b)
    (hψ : ∀ r ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, P) I ψ (r • u))
    (hrad : ∀ r ∈ Ioo a b, mfderiv 𝓘(ℝ, P) I ψ (r • u) (r • u) =
      r • V (ψ (r • u)))
    (γ : ℝ → M) (hγ : IsMIntegralCurveOn γ V (Ioo a b))
    (hinit : ψ (r₀ • u) = γ r₀) :
    EqOn (fun r => ψ (r • u)) γ (Ioo a b) := by
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hr₀ hV
    (isMIntegralCurveOn_normal_ray ψ u V (Ioo a b)
      (fun r hr => (lt_of_le_of_lt ha hr.1).ne') hψ hrad) hγ hinit

/-- The ray comparison only needs field regularity along the ray, so it
also applies to radial fields singular at omitted poles. -/
theorem normal_ray_eq_integralCurve_of_local_field [CompleteSpace E] [IsManifold I 1 M]
    [I.Boundaryless] [T2Space M]
    (ψ : P → M) (u : P) (V : (x : M) → TangentSpace I x)
    {a b r₀ : ℝ} (ha : 0 ≤ a) (hr₀ : r₀ ∈ Ioo a b)
    (hV : ∀ r ∈ Ioo a b, ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun x => (⟨x, V x⟩ : TangentBundle I M)) (ψ (r • u)))
    (hψ : ∀ r ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, P) I ψ (r • u))
    (hrad : ∀ r ∈ Ioo a b, mfderiv 𝓘(ℝ, P) I ψ (r • u) (r • u) =
      r • V (ψ (r • u)))
    (γ : ℝ → M) (hγ : IsMIntegralCurveOn γ V (Ioo a b))
    (hinit : ψ (r₀ • u) = γ r₀) :
    EqOn (fun r => ψ (r • u)) γ (Ioo a b) := by
  exact integralCurve_eqOn_of_contMDiffAt_range hr₀ hV
    (isMIntegralCurveOn_normal_ray ψ u V (Ioo a b)
      (fun r hr => (lt_of_le_of_lt ha hr.1).ne') hψ hrad) hγ hinit

end LichnerowiczObata
