/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataRadial
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # Scalar differential bounds and intrinsic distance -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- A C1 scalar function with nonexpanding differential is nonexpanding for
the intrinsic Riemannian extended distance, directly from its path definition. -/
theorem edist_le_riemannianEDist_of_differential_bound {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ, ℝ) 1 g)
    (hb : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I 𝓘(ℝ, ℝ) g x v‖ ≤ ‖v‖)
    (x y : M) : edist (g x) (g y) ≤ riemannianEDist I x y := by
  rw [riemannianEDist, le_iInf_iff]
  intro γ
  rw [le_iInf_iff]
  intro hγ
  let η : Path (g x) (g y) := γ.map hg.continuous
  have hη : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) 1 η := hg.comp hγ
  have hd : edist (g x) (g y) ≤ ∫⁻ t, ‖mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) η t 1‖ₑ := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ))]
    rw [riemannianEDist]
    exact iInf_le_of_le η (iInf_le _ hη)
  apply hd.trans
  apply lintegral_mono
  intro t
  change ‖mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (g ∘ γ) t 1‖ₑ ≤ _
  rw [mfderiv_comp _ (hg.mdifferentiable (by norm_num) _) (hγ.mdifferentiable (by norm_num) _)]
  simpa only [ContinuousLinearMap.comp_apply, ← ofReal_norm] using
    ENNReal.ofReal_le_ofReal (hb (γ t) (mfderiv (𝓡∂ 1) I γ t 1))

variable [FiniteDimensional ℝ E] [IsManifold I 1 M]

/-- The gradient form of the intrinsic scalar distance estimate. -/
theorem edist_le_riemannianEDist_of_gradient_bound {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ, ℝ) 1 g)
    (hb : ∀ x, ‖gradient (I := I) g x‖ ≤ 1) (x y : M) :
    edist (g x) (g y) ≤ riemannianEDist I x y := by
  apply edist_le_riemannianEDist_of_differential_bound hg _ x y
  intro z v
  rw [norm_tangentSpace_vectorSpace]
  change ‖mvfderiv I g z v‖ ≤ ‖v‖
  rw [← inner_gradient]
  exact (norm_inner_le_norm _ _).trans (by nlinarith [hb z, norm_nonneg v])

end LichnerowiczObata
