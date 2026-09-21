/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module
public import LeanPool.PoincareGeometry.AlmostSchur.Hessian
public import LeanPool.PoincareGeometry.AlmostSchur.HilbertSchmidt

/-! The intrinsic squared tensor norm and trace-free decomposition of the actual Hessian. -/

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

def hessianNormSq (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (f : M → ℝ) (x : M) : ℝ :=
  hilbertSchmidtSq (cov (gradient (I := I) f) x)

def traceFreeHessianNormSq (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (f : M → ℝ) (x : M) : ℝ :=
  hilbertSchmidtSq (traceFree (cov (gradient (I := I) f) x))

/-- This is the full double tensor contraction, not the operator norm. -/
theorem hessianNormSq_eq_sum_sq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (f : M → ℝ) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    hessianNormSq cov f x = ∑ i, ∑ j, (hessian cov f x (b i) (b j)) ^ 2 :=
  hilbertSchmidtSq_eq_sum_sq _ b

/-- Pointwise identity needed before integrating the Bochner formula.
No integrated identity or elliptic solvability is assumed or claimed here. -/
theorem traceFreeHessianNormSq_eq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (f : M → ℝ) (x : M) (hdim : Module.finrank ℝ E ≠ 0) :
    traceFreeHessianNormSq cov f x = hessianNormSq cov f x -
      (laplacian cov f x) ^ 2 / Module.finrank ℝ E := by
  have hrank := VectorBundle.finrank_eq ℝ E (TangentSpace I : M → Type _) x
  have hx : Module.finrank ℝ (TangentSpace I x) ≠ 0 := by rwa [hrank]
  simpa only [traceFreeHessianNormSq, hessianNormSq, laplacian, hrank] using
    hilbertSchmidtSq_traceFree (cov (gradient (I := I) f) x) hx

end AlmostSchur
