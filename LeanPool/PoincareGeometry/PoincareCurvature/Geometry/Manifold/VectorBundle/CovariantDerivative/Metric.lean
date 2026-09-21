/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Along
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Metric-compatible covariant derivatives

This file introduces the basic compatibility condition between a covariant derivative and a
Riemannian metric on a vector bundle.

The condition is stated pointwise: for differentiable sections `σ` and `τ`, the derivative of
their fibrewise inner product along a tangent vector `u` is the sum of the two expected connection
terms.

We also record the corresponding skew-adjointness property for the difference of two
metric-compatible covariant derivatives.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

namespace CovariantDerivative

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- A covariant derivative on a Riemannian vector bundle is metric-compatible if it differentiates
the fibrewise inner product by the Leibniz rule. -/
def IsMetricCompatible (cov : CovariantDerivative I F V) : Prop :=
  ∀ {x : M} {σ τ : Π x : M, V x},
    MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      ∀ u : TangentSpace I x,
        mvfderiv (I := I) (fun y ↦ ⟪σ y, τ y⟫) x u =
          ⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫

variable {cov : CovariantDerivative I F V}

lemma IsMetricCompatible.inner_eq_add (hcov : cov.IsMetricCompatible)
    {x : M} {X : Π x : M, TangentSpace I x} {σ τ : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    mvfderiv (I := I) (fun y ↦ ⟪σ y, τ y⟫) x (X x) =
      ⟪cov.along X σ x, τ x⟫ + ⟪σ x, cov.along X τ x⟫ := by
  simpa [CovariantDerivative.along] using hcov hσ hτ (X x)

section Difference

variable [FiniteDimensional ℝ F]

variable {cov cov' : CovariantDerivative I F V}

@[simp]
lemma difference_apply {x : M} {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) :
    cov.difference cov' x (σ x) = cov σ x - cov' σ x := by
  simpa [CovariantDerivative.difference] using
    (IsCovariantDerivativeOn.difference_apply
      (hcov := cov.isCovariantDerivativeOnUniv)
      (hcov' := cov'.isCovariantDerivativeOnUniv)
      (x := x) (s := Set.univ) (hx := by trivial) (σ := σ) (hσ := hσ))

@[simp]
lemma difference_apply_eq_extend {x : M} (v : V x) :
    cov.difference cov' x v = cov (extend F v) x - cov' (extend F v) x := by
  simpa using
    (difference_apply (cov := cov) (cov' := cov')
      (x := x) (σ := extend F v) (mdifferentiableAt_extend (I := I) (F := F) v))

lemma difference_inner_add_eq_zero
    (hcov : cov.IsMetricCompatible) (hcov' : cov'.IsMetricCompatible)
    (x : M) (u : TangentSpace I x) (v w : V x) :
    ⟪(cov.difference cov' x v) u, w⟫ + ⟪v, (cov.difference cov' x w) u⟫ = 0 := by
  let σ : Π y : M, V y := extend F v
  let τ : Π y : M, V y := extend F w
  have hσ : MDiffAt (T% σ) x := by
    simpa [σ] using (mdifferentiableAt_extend (I := I) (F := F) v)
  have hτ : MDiffAt (T% τ) x := by
    simpa [τ] using (mdifferentiableAt_extend (I := I) (F := F) w)
  have h₁ := hcov (x := x) (σ := σ) (τ := τ) hσ hτ u
  have h₂ := hcov' (x := x) (σ := σ) (τ := τ) hσ hτ u
  have hsub :
      (⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫) -
        (⟪cov' σ x u, τ x⟫ + ⟪σ x, cov' τ x u⟫) = 0 := by
    linarith
  have hdiff :
      ⟪cov σ x u - cov' σ x u, τ x⟫ + ⟪σ x, cov τ x u - cov' τ x u⟫ = 0 := by
    calc
      ⟪cov σ x u - cov' σ x u, τ x⟫ + ⟪σ x, cov τ x u - cov' τ x u⟫
          = (⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫) -
              (⟪cov' σ x u, τ x⟫ + ⟪σ x, cov' τ x u⟫) := by
            simp [inner_sub_left, inner_sub_right]
            ring
      _ = 0 := hsub
  simpa [σ, τ, difference_apply (cov := cov) (cov' := cov') hσ,
    difference_apply (cov := cov) (cov' := cov') hτ] using hdiff

lemma difference_inner_eq_neg
    (hcov : cov.IsMetricCompatible) (hcov' : cov'.IsMetricCompatible)
    (x : M) (u : TangentSpace I x) (v w : V x) :
    ⟪(cov.difference cov' x v) u, w⟫ = -⟪v, (cov.difference cov' x w) u⟫ := by
  have h := difference_inner_add_eq_zero (cov := cov) (cov' := cov') hcov hcov' x u v w
  linarith

end Difference

end CovariantDerivative
