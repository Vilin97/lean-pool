/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.IntrinsicBianchi
public import LeanPool.PoincareGeometry.SchurAssembly
public import LeanPool.PoincareGeometry.SchurThreeDimensional

/-! Schur rigidity and its three-dimensional geometric consequence. -/

@[expose] public noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace SchurRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
  [IsManifold I (minSmoothness ℝ 2) M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [IsManifold I ((3 : ℕ∞) + 1) M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Schur's theorem for a differentiable, not necessarily smooth, Einstein factor. -/
theorem schur [ConnectedSpace M]
    (hLevi : cov.IsLeviCivita) (hn : 3 ≤ Module.finrank ℝ E)
    (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ) f)
    (hRic : ∀ y u v, cov.ricciCurvature y u v = f y * inner ℝ u v) :
    ∃ c : ℝ, ∀ x, f x = c := by
  let x₀ : M := Classical.arbitrary M
  exact ⟨f x₀, fun x ↦ SchurConstancy.eq_of_mfderiv_eq_zero I hf
    (mfderiv_eq_zero_of_einstein cov hLevi hn f hf hRic) x x₀⟩

/-- A connected three-dimensional Einstein manifold has one constant curvature
coefficient for its entire Riemann tensor, hence constant sectional curvature. -/
theorem threeDimensionalEinstein_constantCurvature [ConnectedSpace M]
    (hLevi : cov.IsLeviCivita) (hn : Module.finrank ℝ E = 3)
    (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ) f)
    (hRic : ∀ y u v, cov.ricciCurvature y u v = f y * inner ℝ u v) :
    ∃ K : ℝ, ∀ (x : M) (u v z t : TM x),
      inner ℝ (cov.curvatureTensor x u v z) t =
        K * (inner ℝ u t * inner ℝ v z - inner ℝ u z * inner ℝ v t) := by
  obtain ⟨c, hc⟩ := schur cov hLevi (by omega) f hf hRic
  refine ⟨c / 2, ?_⟩
  intro x u v z t
  apply SchurThreeDimensional.curvature_inner_eq_of_einstein cov hLevi hn x c
  intro a b
  rw [hRic, hc]

end SchurRigidity
