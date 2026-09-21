/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.IntrinsicAngularCoordinates

/-! # Assembling radial, angular, and mixed metric terms -/

@[expose] public noncomputable section
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A linear derivative on angular and radial parameters splits into its
spatial part and a scalar multiple of its unit radial direction. -/
theorem polar_derivative_split (D : P × ℝ →L[ℝ] V) (w : P) (s : ℝ) :
    D (w, s) = D (w, 0) + s • D (0, 1) := by
  rw [← map_smul, ← map_add]
  congr 1
  simp

/-- Unit radial speed and vanishing mixed terms reconstruct the complete
pairing from the angular pairing. No radial or mixed coefficient is assumed
in the conclusion. -/
theorem polar_derivative_full_pairing (D : P × ℝ →L[ℝ] V) (w v : P) (s t A : ℝ)
    (hunit : ‖D (0, 1)‖ = 1)
    (hw : inner ℝ (D (w, 0)) (D (0, 1)) = 0)
    (hv : inner ℝ (D (v, 0)) (D (0, 1)) = 0)
    (hang : inner ℝ (D (w, 0)) (D (v, 0)) = A) :
    inner ℝ (D (w, s)) (D (v, t)) = A + s * t := by
  have hv' : inner ℝ (D (0, 1)) (D (v, 0)) = 0 := by
    rw [real_inner_comm]
    exact hv
  rw [polar_derivative_split D w s, polar_derivative_split D v t]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hw, hv', hang, real_inner_self_eq_norm_sq,
    hunit, one_pow, mul_zero, mul_one, add_zero, zero_add]
  ring

section Manifold
open AlmostSchur Bundle
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- For a differentiable polar map, its radius identity forces the spatial
derivatives to be orthogonal to the radial gradient. -/
theorem polar_map_spatial_orthogonal {Γ : P × ℝ → M} {ρ : M → ℝ} {u : P} {r : ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Γ (u, r))
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ (Γ (u, r)))
    (hlevel : (ρ ∘ Γ) =ᶠ[𝓝 (u, r)] Prod.snd) (w : P) :
    inner ℝ (gradient (I := I) ρ (Γ (u, r)))
      (mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (w, 0)) = 0 := by
  rw [inner_gradient]
  have hd := mfderiv_comp_apply (u, r) hρ hΓ (w, 0)
  rw [hlevel.mfderiv_eq, mfderiv_eq_fderiv, fderiv_snd] at hd
  exact hd.symm

/-- The radius identity, radial gradient velocity, unit speed, and angular
pairing give the complete metric of an actual manifold polar map. Mixed
terms are derived rather than supplied as hypotheses. -/
theorem polar_map_full_pairing {Γ : P × ℝ → M} {ρ : M → ℝ} {u : P} {r : ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Γ (u, r))
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ (Γ (u, r)))
    (hlevel : (ρ ∘ Γ) =ᶠ[𝓝 (u, r)] Prod.snd)
    (hrad : mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (0, 1) = gradient (I := I) ρ (Γ (u, r)))
    (hunit : ‖mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (0, 1)‖ = 1)
    (w v : P) (s t A : ℝ)
    (hang : inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (w, 0))
      (mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (v, 0)) = A) :
    inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (w, s))
      (mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (v, t)) = A + s * t := by
  have horth (j : P) : inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (j, 0))
      (mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (0, 1)) = 0 := by
    rw [hrad, real_inner_comm]
    exact polar_map_spatial_orthogonal hΓ hρ hlevel j
  exact polar_derivative_full_pairing _ w v s t A hunit (horth w) (horth v) hang

end Manifold

section Slices
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A spatial slice differentiates to the spatial part of the joint derivative. -/
theorem polar_map_spatial_derivative {Γ : P × ℝ → M} {u : P} {r : ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Γ (u, r)) (w : P) :
    mfderiv 𝓘(ℝ, P) I (fun y => Γ (y, r)) u w =
      mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (w, 0) := by
  have hi := hasFDerivAt_prodMk_left (𝕜 := ℝ) u r
  have hd := mfderiv_comp_apply (f := fun y : P => (y, r)) (g := Γ) u hΓ
    (mdifferentiableAt_iff_differentiableAt.mpr hi.differentiableAt) w
  rw [mfderiv_eq_fderiv, hi.fderiv] at hd
  exact hd

/-- A radial slice differentiates to the radial part of the joint derivative. -/
theorem polar_map_radial_derivative {Γ : P × ℝ → M} {u : P} {r : ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Γ (u, r)) (s : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I (fun t => Γ (u, t)) r s =
      mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (0, s) := by
  have hi := hasFDerivAt_prodMk_right (𝕜 := ℝ) u r
  have hd := mfderiv_comp_apply (f := fun t : ℝ => (u, t)) (g := Γ) r hΓ
    (mdifferentiableAt_iff_differentiableAt.mpr hi.differentiableAt) s
  rw [mfderiv_eq_fderiv, hi.fderiv] at hd
  exact hd

/-- Integral-curve velocity identifies the joint radial derivative on an
open radial interval, without a separate derivative hypothesis. -/
theorem polar_map_radial_derivative_of_integralCurve
    {Γ : P × ℝ → M} {u : P} {r ℓ : ℝ}
    {X : (x : M) → TangentSpace I x}
    (hΓ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Γ (u, r))
    (hcurve : IsMIntegralCurveOn (fun t => Γ (u, t)) X (Set.Ioo 0 ℓ))
    (hr : r ∈ Set.Ioo 0 ℓ) :
    mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (0, 1) = X (Γ (u, r)) := by
  rw [← polar_map_radial_derivative hΓ 1]
  rw [((hcurve r hr).hasMFDerivAt (isOpen_Ioo.mem_nhds hr)).mfderiv]
  change (1 : ℝ) • X (Γ (u, r)) = X (Γ (u, r))
  exact one_smul ℝ _

end Slices

section SliceAssembly
open AlmostSchur Bundle
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Assemble the full metric directly from the radial integral curve and
the angular slice pairing, matching the data of the spherical product. -/
theorem polar_map_full_pairing_of_slices {Γ : P × ℝ → M} {ρ : M → ℝ}
    {u : P} {r ℓ : ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Γ (u, r))
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ (Γ (u, r)))
    (hlevel : (ρ ∘ Γ) =ᶠ[𝓝 (u, r)] Prod.snd)
    (hcurve : IsMIntegralCurveOn (fun t => Γ (u, t))
      (gradient (I := I) ρ) (Set.Ioo 0 ℓ))
    (hr : r ∈ Set.Ioo 0 ℓ)
    (hunit : ‖mfderiv 𝓘(ℝ, ℝ) I (fun t => Γ (u, t)) r 1‖ = 1)
    (w v : P) (s t A : ℝ)
    (hang : inner ℝ (mfderiv 𝓘(ℝ, P) I (fun y => Γ (y, r)) u w)
      (mfderiv 𝓘(ℝ, P) I (fun y => Γ (y, r)) u v) = A) :
    inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (w, s))
      (mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (v, t)) = A + s * t := by
  have hrad := polar_map_radial_derivative_of_integralCurve hΓ hcurve hr
  have hu : ‖mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (0, 1)‖ = 1 := by
    rw [← polar_map_radial_derivative hΓ 1]
    exact hunit
  have ha : inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (w, 0))
      (mfderiv 𝓘(ℝ, P × ℝ) I Γ (u, r) (v, 0)) = A := by
    rw [← polar_map_spatial_derivative hΓ w, ← polar_map_spatial_derivative hΓ v]
    exact hang
  exact polar_map_full_pairing hΓ hρ hlevel hrad hu w v s t A ha

end SliceAssembly
end LichnerowiczObata
