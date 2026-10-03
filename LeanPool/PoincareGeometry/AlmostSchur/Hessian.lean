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

public import LeanPool.PoincareGeometry.AlmostSchur.Gradient
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Covariant Hessian and Laplace–Beltrami trace

These are constructed from the actual gradient and connection. Symmetry,
regularity, volume integration and elliptic solvability remain separate proof
obligations. In particular, defining an operator does not prove Poisson solvability.
-/

@[expose] public noncomputable section
open Bundle
open scoped Manifold ContDiff BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local instance (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x

/-- The covariant Hessian relative to the given connection:
`Hess f(u,v) = g(∇_u grad f,v)`. -/
def hessian (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (f : M → ℝ) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (innerSL ℝ).comp (cov (gradient (I := I) f) x)

theorem hessian_apply (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (f : M → ℝ) (x : M) (u v : TangentSpace I x) :
    hessian cov f x u v = inner ℝ (cov (gradient (I := I) f) x u) v := rfl

/-- The trace of `∇ grad`, with the `div grad` sign convention.
For a Levi–Civita connection this is the geometric Laplace–Beltrami operator. -/
def laplacian (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (f : M → ℝ) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (cov (gradient (I := I) f) x).toLinearMap

/-- Every orthonormal frame computes the same Laplace–Beltrami trace. -/
theorem laplacian_eq_sum_hessian
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (f : M → ℝ) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    laplacian cov f x = ∑ i, hessian cov f x (b i) (b i) := by
  rw [laplacian, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_comm _ _

/-- Independence also holds when the two bases have different index types. -/
theorem sum_hessian_basis_independent
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (f : M → ℝ) (x : M) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (c : OrthonormalBasis κ ℝ (TangentSpace I x)) :
    (∑ i, hessian cov f x (b i) (b i)) = ∑ j, hessian cov f x (c j) (c j) := by
  rw [← laplacian_eq_sum_hessian, ← laplacian_eq_sum_hessian]

end AlmostSchur
