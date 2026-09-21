/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SpherePolarTangent
public import Mathlib.Topology.VectorBundle.Riemannian

/-! # Transfer of the polar metric to the comparison derivative -/

@[expose] public noncomputable section
open Bundle
open scoped Manifold Topology
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- A locally intertwined polar comparison preserves the metric on all
tangent vectors once the parameter derivative is nonsingular and the two
polar pullback metrics agree. -/
theorem polar_comparison_derivative_inner
    {Φ : P × ℝ → M} {Ψ : P × ℝ → Z} {T : M → Z}
    (u : Metric.sphere (0 : P) 1) (r : ℝ)
    (hDim : Module.finrank ℝ E = n + 1)
    (hΦ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ ((u : P), r))
    (hΨ : MDifferentiableAt 𝓘(ℝ, P × ℝ) 𝓘(ℝ, Z) Ψ ((u : P), r))
    (hT : MDifferentiableAt I 𝓘(ℝ, Z) T (Φ ((u : P), r)))
    (hD : Set.InjOn (mfderiv 𝓘(ℝ, P × ℝ) I Φ ((u : P), r))
      {q : P × ℝ | inner ℝ (u : P) q.1 = 0})
    (hmetric : ∀ w v : P, inner ℝ (u : P) w = 0 → inner ℝ (u : P) v = 0 →
      ∀ s t : ℝ,
        inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I Φ ((u : P), r) (w, s))
          (mfderiv 𝓘(ℝ, P × ℝ) I Φ ((u : P), r) (v, t)) =
        inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) 𝓘(ℝ, Z) Ψ ((u : P), r) (w, s))
          (mfderiv 𝓘(ℝ, P × ℝ) 𝓘(ℝ, Z) Ψ ((u : P), r) (v, t)))
    (hlocal : (fun q : Metric.sphere (0 : P) 1 × ℝ => T (Φ (q.1, q.2)))
      =ᶠ[𝓝 (u, r)] (fun q => Ψ (q.1, q.2)))
    (v w : TangentSpace I (Φ ((u : P), r))) :
    inner ℝ (mfderiv I 𝓘(ℝ, Z) T (Φ ((u : P), r)) v)
      (mfderiv I 𝓘(ℝ, Z) T (Φ ((u : P), r)) w) = inner ℝ v w := by
  let Φₛ := fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)
  let Ψₛ := fun q : Metric.sphere (0 : P) 1 × ℝ => Ψ (q.1, q.2)
  obtain ⟨D, hDeq, hDeriv⟩ := exists_sphere_polar_derivative_equiv u r hDim hΦ hD
  obtain ⟨v₀, rfl⟩ := D.surjective v
  obtain ⟨w₀, rfl⟩ := D.surjective w
  have hchain : (mfderiv I 𝓘(ℝ, Z) T (Φ ((u : P), r))).comp
      (D : _ →L[ℝ] _) = mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Z) Ψₛ (u, r) := by
    rw [hDeq, ← mfderiv_comp (u, r) hT
      (mdifferentiableAt_sphere_polar_restriction u r hΦ)]
    exact hlocal.mfderiv_eq
  change inner ℝ (((mfderiv I 𝓘(ℝ, Z) T (Φ ((u : P), r))).comp (D : _ →L[ℝ] _)) v₀)
    (((mfderiv I 𝓘(ℝ, Z) T (Φ ((u : P), r))).comp (D : _ →L[ℝ] _)) w₀) = _
  rw [hchain]
  have hDv := congrArg (fun L => L v₀) hDeq
  have hDw := congrArg (fun L => L w₀) hDeq
  change D v₀ = mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I Φₛ (u, r) v₀ at hDv
  change D w₀ = mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I Φₛ (u, r) w₀ at hDw
  change inner ℝ (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Z) Ψₛ (u, r) v₀)
    (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Z) Ψₛ (u, r) w₀) = inner ℝ (D v₀) (D w₀)
  rw [hDv, hDw, mfderiv_sphere_polar_restriction u r hΦ,
    mfderiv_sphere_polar_restriction u r hΨ]
  exact (hmetric _ _ (spherePolarTangentInclusion_orthogonal u v₀)
    (spherePolarTangentInclusion_orthogonal u w₀) _ _).symm

end LichnerowiczObata
