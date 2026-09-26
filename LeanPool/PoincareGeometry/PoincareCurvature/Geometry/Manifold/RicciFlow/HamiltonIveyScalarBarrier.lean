/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveySpectrum
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarParabolicBarrier

/-!
# Scalar-curvature lower barrier for Hamilton--Ivey

This file specializes the compact parabolic Riccati maximum principle to the
actual scalar curvature of a three-dimensional metric family.  Assuming the
genuine scalar evolution equation

`partial_t R = Delta R + 2 |Ric|^2`,

the intrinsic estimate `R^2 <= 3 |Ric|^2` supplies the required reaction
inequality and yields the sharp compact lower barrier

`R(t) >= -3 K / (1 + 2 K t)`.

Thus the maximum-principle layer no longer assumes a scalar supersolution as
an unrelated function; the remaining input is precisely the geometric scalar
evolution identity which the curvature-variation layer must prove.
-/

@[expose] public noncomputable section
open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- The scalar Hamilton--Ivey lower barrier for an actual three-dimensional
Ricci-flow scalar curvature satisfying its geometric evolution equation. -/
theorem scalarCurvature_lowerBarrier_of_evolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K T : ℝ} (hK : 0 ≤ K)
    (hcont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (htime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt (fun s => g.scalarCurvature cov hcov s x)
        (g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
          2 * g.ricciNormSq cov hcov t x) t)
    (hfNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in nhds x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hdf : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (hinitial : ∀ x : M,
      -(3 : ℝ) * K ≤ g.scalarCurvature cov hcov 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      -(3 : ℝ) * K / (1 + 2 * K * t) ≤
        g.scalarCurvature cov hcov t x := by
  let f : ℝ → M → ℝ := g.scalarCurvature cov hcov
  let ft : ℝ → M → ℝ := fun t x =>
    g.scalarLaplacian cov f t x + 2 * g.ricciNormSq cov hcov t x
  apply g.parabolicRiccatiLowerBarrier cov f ft
    (n := (3 : ℝ)) (C := K) (T := T) (by norm_num) hK
  · exact hcont
  · intro t ht x
    exact htime t ht x
  · exact hfNear
  · exact hdf
  · intro t ht x
    have hreaction := g.two_thirds_scalarCurvature_sq_le_two_mul_ricciNormSq
      cov hcov hdim t x
    dsimp only [f, ft]
    linarith
  · exact hinitial

end CovariantDerivative.TimeDependentRiemannianMetric
