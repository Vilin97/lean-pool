/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions

/-! Differentiating a variable multiple of the metric using the actual connection. -/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff BigOperators

namespace SchurRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The section formula for the covariant derivative of a bilinear tensor field.
The derivative here is the manifold derivative, not an abstract operation. -/
def bilinearDerivative (cov : CovariantDerivative I E TM)
    (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (U V : ∀ x : M, TM x) (x : M) (w : TM x) : ℝ :=
  mvfderiv (I := I) (fun y ↦ A y (U y) (V y)) x w -
    A x (cov U x w) (V x) - A x (U x) (cov V x w)

/-- The section formula is local in both sections. -/
theorem bilinearDerivative_congr_of_eventuallyEq
    (cov : CovariantDerivative I E TM)
    (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (U V U' V' : ∀ x : M, TM x) (x : M) (w : TM x)
    (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x)
    (hU' : MDiffAt (T% U') x) (hV' : MDiffAt (T% V') x)
    (heU : ∀ᶠ y in nhds x, U y = U' y)
    (heV : ∀ᶠ y in nhds x, V y = V' y) :
    bilinearDerivative cov A U V x w = bilinearDerivative cov A U' V' x w := by
  have hdU := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hU hU'
    (Filter.univ_mem : Set.univ ∈ nhds x) heU
  have hdV := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hV hV'
    (Filter.univ_mem : Set.univ ∈ nhds x) heV
  have he : (fun y ↦ A y (U y) (V y)) =ᶠ[nhds x]
      (fun y ↦ A y (U' y) (V' y)) := by
    filter_upwards [heU, heV] with y hy hz
    rw [hy, hz]
  have hd := he.mfderiv_eq (I := I) (I' := 𝓘(ℝ))
  unfold bilinearDerivative mvfderiv
  rw [hdU, hdV, heU.self_of_nhds, heV.self_of_nhds, hd]
  rfl

/-- Covariant differentiation respects subtraction of differentiable tensor evaluations. -/
theorem bilinearDerivative_sub
    (cov : CovariantDerivative I E TM)
    (A B : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (U V : ∀ x : M, TM x) (x : M) (w : TM x)
    (hA : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ A y (U y) (V y)) x)
    (hB : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ B y (U y) (V y)) x) :
    bilinearDerivative cov (fun y ↦ A y - B y) U V x w =
      bilinearDerivative cov A U V x w - bilinearDerivative cov B U V x w := by
  unfold bilinearDerivative
  simp only [LinearMap.sub_apply]
  rw [mvfderiv_fun_sub hA hB]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-- The metric as a bilinear tensor field. -/
def metricTensor (x : M) : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ := innerₗ (TM x)

/-- The Einstein tensor built from the actual Ricci and scalar curvatures. -/
def einsteinTensor (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (x : M) : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ :=
  cov.ricciCurvature x - (cov.scalarCurvature x / 2) • metricTensor x

@[simp] theorem einsteinTensor_apply (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (x : M) (u v : TM x) :
    einsteinTensor cov x u v =
      cov.ricciCurvature x u v - cov.scalarCurvature x / 2 * inner ℝ u v := rfl

/-- Metric compatibility gives the true product rule `∇(λg) = dλ ⊗ g`. -/
theorem bilinearDerivative_eq_of_eq_mul_inner
    (cov : CovariantDerivative I E TM) (hmetric : cov.IsMetricCompatibleTangent)
    (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ) (f : M → ℝ)
    (hA : ∀ y u v, A y u v = f y * inner ℝ u v)
    (U V : ∀ x : M, TM x) (x : M) (w : TM x)
    (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) :
    bilinearDerivative cov A U V x w =
      mvfderiv (I := I) f x w * inner ℝ (U x) (V x) := by
  have hi := CovariantDerivative.mdiffAt_inner_sections hU hV
  have hm := hmetric hU hV w
  unfold bilinearDerivative
  simp only [hA]
  rw [mvfderiv_fun_mul hf hi]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [hm]
  ring

/-- In the Einstein condition the genuine scalar curvature is `n λ`. -/
theorem scalarCurvature_eq_dim_mul
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (f : M → ℝ)
    (hRic : ∀ y u v, cov.ricciCurvature y u v = f y * inner ℝ u v)
    (x : M) :
    cov.scalarCurvature x = (Module.finrank ℝ E : ℝ) * f x := by
  classical
  rw [CovariantDerivative.scalarCurvature_eq_sum]
  simp only [hRic, (stdOrthonormalBasis ℝ (TM x)).inner_eq_ite]
  simp only [ite_true, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rfl

/-- Contracting `∇(λg)` against an orthonormal frame gives precisely `dλ`.
Only orthonormality at the evaluation point is used; no parallel-frame hypothesis is hidden. -/
theorem sum_bilinearDerivative_eq_differential
    (cov : CovariantDerivative I E TM) (hmetric : cov.IsMetricCompatibleTangent)
    (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ) (f : M → ℝ)
    (hA : ∀ y u v, A y u v = f y * inner ℝ u v)
    {ι : Type*} [Fintype ι] (x : M) (b : OrthonormalBasis ι ℝ (TM x))
    (e : ι → ∀ y : M, TM y) (he : ∀ i, e i x = b i)
    (heDiff : ∀ i, MDiffAt (T% (e i)) x)
    (W : ∀ y : M, TM y) (hW : MDiffAt (T% W) x)
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    (∑ i, bilinearDerivative cov A (e i) W x (e i x)) =
      mvfderiv (I := I) f x (W x) := by
  simp_rw [bilinearDerivative_eq_of_eq_mul_inner cov hmetric A f hA
    _ W x _ hf (heDiff _) hW, he]
  have h := congrArg (fun v ↦ mvfderiv (I := I) f x v) (b.sum_repr' (W x))
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using h

end SchurRigidity
