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

public import LeanPool.PoincareGeometry.AlmostSchur.MetricRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.UniformQuadraticBound
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Algebra.Order.Star.Real

/-! # Uniform ellipticity of the actual chart-density cometric

The coefficient matrix is the positive Riemannian density times the inverse
of the actual coordinate Gram matrix. Positivity and compact uniform bounds
are derived from these definitions, not supplied as PDE assumptions.
-/

@[expose] public noncomputable section
open Bundle Set Matrix
open scoped BigOperators Manifold

namespace AlmostSchur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A continuous positive-definite matrix family has a compact uniform
quadratic lower bound in the Euclidean norm of its coefficient vector. -/
theorem exists_uniform_posDef_matrix_lower_bound
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (A : X → Matrix ι ι ℝ) (hA : ContinuousOn A K)
    (hp : ∀ x ∈ K, (A x).PosDef) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ v : EuclideanSpace ℝ ι,
      C * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, A x i j * v i * v j := by
  apply exists_uniform_quadratic_lower_bound hK
    (fun x (v : EuclideanSpace ℝ ι) => ∑ i, ∑ j, A x i j * v i * v j)
  · apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    have he : ContinuousOn (fun p : X × EuclideanSpace ℝ ι => A p.1 i j)
        (K ×ˢ Metric.sphere (0 : EuclideanSpace ℝ ι) 1) :=
      ((continuousOn_pi.mp (continuousOn_pi.mp hA i) j).comp continuous_fst.continuousOn
        (fun p hp => hp.1))
    exact (he.mul ((PiLp.continuous_apply 2 _ i).comp continuous_snd).continuousOn).mul
      ((PiLp.continuous_apply 2 _ j).comp continuous_snd).continuousOn
  · intro x hx v hv
    have hv' : (fun i => v i) ≠ 0 := by
      intro he
      apply hv
      ext i
      exact congrFun he i
    have h := (hp x hx).dotProduct_mulVec_pos hv'
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm, mul_assoc] using h
  · intro x hx a v
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- A continuous matrix family has a compact uniform absolute quadratic upper bound. -/
theorem exists_uniform_matrix_quadratic_upper_bound
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (A : X → Matrix ι ι ℝ) (hA : ContinuousOn A K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ v : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * v i * v j| ≤ C * ‖v‖ ^ 2 := by
  apply exists_uniform_quadratic_upper_bound hK
    (fun x (v : EuclideanSpace ℝ ι) => ∑ i, ∑ j, A x i j * v i * v j)
  · apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    have he : ContinuousOn (fun p : X × EuclideanSpace ℝ ι => A p.1 i j)
        (K ×ˢ Metric.sphere (0 : EuclideanSpace ℝ ι) 1) :=
      ((continuousOn_pi.mp (continuousOn_pi.mp hA i) j).comp continuous_fst.continuousOn
        (fun p hp => hp.1))
    exact (he.mul ((PiLp.continuous_apply 2 _ i).comp continuous_snd).continuousOn).mul
      ((PiLp.continuous_apply 2 _ j).comp continuous_snd).continuousOn
  · intro x hx a v
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The actual divergence-form coefficient matrix in a fixed coordinate basis. -/
def coordinateEllipticMatrix (b : Module.Basis ι ℝ E) (c : M) (z : E) : Matrix ι ι ℝ :=
  matrixDensity (coordinateMetric (I := I) b c z) • (coordinateMetric (I := I) b c z)⁻¹

/-- Entrywise form of the actual density-weighted inverse Gram matrix. -/
theorem coordinateEllipticMatrix_apply (b : Module.Basis ι ℝ E) (c : M) (z : E)
    (i j : ι) : coordinateEllipticMatrix (I := I) b c z i j =
      matrixDensity (coordinateMetric (I := I) b c z) * (coordinateMetric (I := I) b c z)⁻¹ i j := rfl

/-- Pointwise ellipticity follows from the actual tangent metric's positive definiteness. -/
theorem coordinateEllipticMatrix_posDef (b : Module.Basis ι ℝ E) (c : M) (z : E)
    (hz : z ∈ (extChartAt I c).target) : (coordinateEllipticMatrix (I := I) b c z).PosDef :=
  (coordinateMetric_posDef b c z hz).inv.smul (coordinateMetric_density_pos b c z hz)

variable [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

/-- The true coordinate inverse metric is continuous on the chart target. -/
theorem continuousOn_coordinateMetric_inv (b : Module.Basis ι ℝ E) (c : M) :
    ContinuousOn (fun z => (coordinateMetric (I := I) b c z)⁻¹) (extChartAt I c).target := by
  intro z hz
  apply (continuousAt_matrix_inv _ ?_).comp_continuousWithinAt
    (continuousOn_coordinateMetric b c z hz)
  simpa only [Ring.inverse_eq_inv'] using
    (continuousAt_inv₀ (coordinateMetric_posDef b c z hz).det_pos.ne')

/-- The density-weighted coefficient matrix is continuous on its actual domain. -/
theorem continuousOn_coordinateEllipticMatrix (b : Module.Basis ι ℝ E) (c : M) :
    ContinuousOn (coordinateEllipticMatrix (I := I) b c) (extChartAt I c).target :=
  (continuousOn_coordinateDensity b c).smul (continuousOn_coordinateMetric_inv b c)

/-- Every compact subset of the chart target has a proved positive ellipticity constant. -/
theorem exists_coordinateEllipticMatrix_lower_bound (b : Module.Basis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ v : EuclideanSpace ℝ ι,
      C * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, coordinateEllipticMatrix (I := I) b c z i j * v i * v j :=
  exists_uniform_posDef_matrix_lower_bound hK _
    ((continuousOn_coordinateEllipticMatrix b c).mono hKt)
    (fun z hz => coordinateEllipticMatrix_posDef b c z (hKt hz))

/-- Every compact chart subset has a finite upper bound for the actual energy quadratic form. -/
theorem exists_coordinateEllipticMatrix_upper_bound (b : Module.Basis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ v : EuclideanSpace ℝ ι,
      (∑ i, ∑ j, coordinateEllipticMatrix (I := I) b c z i j * v i * v j) ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_uniform_matrix_quadratic_upper_bound hK _
    ((continuousOn_coordinateEllipticMatrix (I := I) b c).mono hKt)
  exact ⟨C, hC0, fun z hz v => (le_abs_self _).trans (hC z hz v)⟩

end AlmostSchur
