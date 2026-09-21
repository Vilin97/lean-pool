/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.RicciDerivative
import LeanPool.PoincareGeometry.ContractedBianchiSections

/-! The geometric contracted Bianchi identity and divergence of Einstein's tensor.
All derivatives are actual manifold derivatives, with the connection slot corrections. -/

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

/-- The covariant divergence, contracted in a supplied orthonormal basis.
The two differentiated tensor arguments are extended by actual smooth fields. -/
def divergenceInBasis (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {ι : Type} [Fintype ι] (x : M) (b : OrthonormalBasis ι ℝ (TM x)) (w : TM x) : ℝ :=
  ∑ i, bilinearDerivative cov A (CovariantDerivative.schurFrame x b.toBasis i)
    (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) x (b i)

theorem scalarCurvature_mdifferentiableAt (x : M) :
    MDifferentiableAt I 𝓘(ℝ) cov.scalarCurvature x := by
  let b := stdOrthonormalBasis ℝ (TM x)
  have h := mdifferentiableAt_metricTrace_schurFrame cov.ricciCurvature x b (by
    intro i j
    exact cov.ricciDerivative_ricci_mdiffAt _ _ x
      ((CovariantDerivative.schurFrame_contMDiff_three x b.toBasis i).of_le (by norm_num))
      (CovariantDerivative.schurFrame_contMDiff_three x b.toBasis j))
  have heq : cov.scalarCurvature = metricTrace cov.ricciCurvature :=
    funext (scalarCurvature_eq_metricTrace cov)
  rwa [← heq] at h

/-- The derivative of actual scalar curvature is the metric trace of the actual
covariant derivative of Ricci. -/
theorem scalarCurvature_derivative_eq_trace
    (hmetric : cov.IsMetricCompatibleTangent)
    {ι : Type} [Fintype ι] [DecidableEq ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TM x)) (w : TM x) :
    mvfderiv (I := I) cov.scalarCurvature x w =
      ∑ i, bilinearDerivative cov cov.ricciCurvature
        (CovariantDerivative.schurFrame x b.toBasis i)
        (CovariantDerivative.schurFrame x b.toBasis i) x w := by
  have h := mvfderiv_metricTrace_eq_sum_schurFrame cov hmetric cov.ricciCurvature x b (by
    intro i j
    exact cov.ricciDerivative_ricci_mdiffAt _ _ x
      ((CovariantDerivative.schurFrame_contMDiff_three x b.toBasis i).of_le (by norm_num))
      (CovariantDerivative.schurFrame_contMDiff_three x b.toBasis j)) w
  have heq : cov.scalarCurvature = metricTrace cov.ricciCurvature :=
    funext (scalarCurvature_eq_metricTrace cov)
  rwa [← heq] at h

/-- The actual twice-contracted Bianchi identity, with no postulated derivative
bridge and valid for every orthonormal tangent basis. -/
theorem scalarCurvature_derivative_eq_two_divergenceRicci
    (hLevi : cov.IsLeviCivita)
    {ι : Type} [Fintype ι] [DecidableEq ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TM x)) (w : TM x) :
    mvfderiv (I := I) cov.scalarCurvature x w =
      2 * divergenceInBasis cov cov.ricciCurvature x b w := by
  let e := CovariantDerivative.schurFrame (I := I) x b.toBasis
  let W := CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w
  have he (i : ι) : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (e i)) :=
    CovariantDerivative.schurFrame_contMDiff_three x b.toBasis i
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W) :=
    CovariantDerivative.smoothExtend_contMDiff_three x w
  have hex (i : ι) : e i x = b i := CovariantDerivative.schurFrame_at x b.toBasis i
  have hWx : W x = w := CovariantDerivative.smoothExtend_apply x w
  have hscalar := scalarCurvature_derivative_eq_trace cov hLevi.2 x b w
  have hi (i : ι) := cov.ricciDerivative_eq_trace_schurFrame hLevi.2 x b
    W (e i) (e i) (hW.of_le (by norm_num)) (he i) (he i)
  simp only [hWx] at hi
  change mvfderiv (I := I) cov.scalarCurvature x w =
    ∑ i, bilinearDerivative cov cov.ricciCurvature (e i) (e i) x w at hscalar
  simp_rw [hi] at hscalar
  have hj (i : ι) := cov.ricciDerivative_eq_trace_schurFrame hLevi.2 x b
    (e i) (e i) W ((he i).of_le (by norm_num)) (he i) hW
  simp only [hex] at hj
  have hb := cov.curvatureCovariantDerivativeInner_doubleContraction_sections
    x hLevi.1 hLevi.2 e W he hW
  simp only [hex] at hb
  rw [hscalar]
  change (∑ i, ∑ k, inner ℝ (cov.secondBianchiAux W (e k) (e i) (e i) x) (b k)) =
    2 * ∑ i, bilinearDerivative cov cov.ricciCurvature (e i) W x (b i)
  simp_rw [hj]
  exact hb

theorem divergenceRicci_eq_half_differential_scalarCurvature
    (hLevi : cov.IsLeviCivita)
    {ι : Type} [Fintype ι] [DecidableEq ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TM x)) (w : TM x) :
    divergenceInBasis cov cov.ricciCurvature x b w =
      (1 / 2 : ℝ) * mvfderiv (I := I) cov.scalarCurvature x w := by
  have h := scalarCurvature_derivative_eq_two_divergenceRicci cov hLevi x b w
  linarith

/-- The actual Einstein tensor is divergence-free for every orthonormal basis. -/
theorem divergenceEinstein_eq_zero
    (hLevi : cov.IsLeviCivita)
    {ι : Type} [Fintype ι] [DecidableEq ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TM x)) (w : TM x) :
    divergenceInBasis cov (einsteinTensor cov) x b w = 0 := by
  let e := CovariantDerivative.schurFrame (I := I) x b.toBasis
  let W := CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w
  let f := fun y ↦ cov.scalarCurvature y / 2
  let B := fun y ↦ f y • metricTensor (I := I) y
  have hf : MDifferentiableAt I 𝓘(ℝ) f x := by
    simpa only [f, div_eq_mul_inv, Pi.mul_apply] using!
      (scalarCurvature_mdifferentiableAt cov x).mul
        (mdifferentiableAt_const (c := (2 : ℝ)⁻¹))
  have he (i : ι) : MDiffAt (T% (e i)) x :=
    ((CovariantDerivative.schurFrame_contMDiff_three x b.toBasis i) x).mdifferentiableAt
      (by norm_num)
  have hW : MDiffAt (T% W) x :=
    ((CovariantDerivative.smoothExtend_contMDiff_three x w) x).mdifferentiableAt (by norm_num)
  have hex (i : ι) : e i x = b i := CovariantDerivative.schurFrame_at x b.toBasis i
  have hWx : W x = w := CovariantDerivative.smoothExtend_apply x w
  have hBeq : ∀ y u v, B y u v = f y * inner ℝ u v := fun _ _ _ ↦ rfl
  have hB (i : ι) : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ B y (e i y) (W y)) x := by
    simp only [hBeq]
    exact hf.mul (CovariantDerivative.mdiffAt_inner_sections (he i) hW)
  have hRic (i : ι) : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ cov.ricciCurvature y (e i y) (W y)) x :=
    cov.ricciDerivative_ricci_evaluation_regular x (e i) W (he i) hW
  have hdivB := sum_bilinearDerivative_eq_differential cov hLevi.2 B f hBeq
    x b e hex he W hW hf
  simp only [hex, hWx] at hdivB
  have hdf : mvfderiv (I := I) f x w =
      (1 / 2 : ℝ) * mvfderiv (I := I) cov.scalarCurvature x w := by
    change mvfderiv (I := I) (fun y ↦ cov.scalarCurvature y / 2) x w = _
    simp only [div_eq_mul_inv]
    rw [mvfderiv_fun_mul (scalarCurvature_mdifferentiableAt cov x) mdifferentiableAt_const]
    simp only [add_apply, smul_apply, smul_eq_mul, mvfderiv_const, zero_apply,
      mul_zero, zero_add, one_mul]
  change (∑ i, bilinearDerivative cov (fun y ↦ cov.ricciCurvature y - B y)
    (e i) W x (b i)) = 0
  simp_rw [bilinearDerivative_sub cov cov.ricciCurvature B _ W x _ (hRic _) (hB _)]
  rw [Finset.sum_sub_distrib, hdivB, hdf]
  change divergenceInBasis cov cov.ricciCurvature x b w -
    (1 / 2 : ℝ) * mvfderiv (I := I) cov.scalarCurvature x w = 0
  rw [divergenceRicci_eq_half_differential_scalarCurvature cov hLevi x b w]
  exact sub_self _

/-- Basis independence is a consequence of the geometric Ricci identity itself. -/
theorem divergenceRicci_basis_independent
    (hLevi : cov.IsLeviCivita)
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (x : M) (b : OrthonormalBasis ι ℝ (TM x)) (c : OrthonormalBasis κ ℝ (TM x))
    (w : TM x) :
    divergenceInBasis cov cov.ricciCurvature x b w =
      divergenceInBasis cov cov.ricciCurvature x c w := by
  rw [divergenceRicci_eq_half_differential_scalarCurvature cov hLevi x b w,
    divergenceRicci_eq_half_differential_scalarCurvature cov hLevi x c w]

end SchurRigidity
