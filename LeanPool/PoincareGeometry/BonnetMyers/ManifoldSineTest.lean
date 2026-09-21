/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.ParallelFieldContinuation
import LeanPool.PoincareGeometry.BonnetMyers.IndexForm

/-!
# Sine test fields along an actual global geodesic

The scalar index-form calculation is useful geometrically only after its
Dirichlet field has been turned into a tangent-bundle-valued field along a
geodesic.  This module carries out that step using the genuine global parallel
transport constructed in `ParallelFieldContinuation`.  In particular, the
field below has zero endpoints and its displayed derivative is an intrinsic
covariant derivative, rather than a calculation in a fixed proxy vector
space.

This does not yet prove the second-variation inequality: that still requires
an endpoint-minimizing smooth geodesic and a manifold variation theorem.
-/

noncomputable section

open Bundle Manifold Set Filter
open MeasureTheory
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace BigOperators

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace IntrinsicGeodesic.GlobalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- The Dirichlet sine test multiplied by an actual global parallel field. -/
def GlobalParallelField.sineTestField
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀) (L : ℝ) :
    ∀ s : ℝ, TM (curve (shift γ t₀) s) :=
  fun s ↦ sineTest L s • p.field s

/-- The intrinsic covariant derivative prescribed for `sineTestField`. -/
def GlobalParallelField.sineTestDerivativeField
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀) (L : ℝ) :
    ∀ s : ℝ, TM (curve (shift γ t₀) s) :=
  fun s ↦ sineTestDeriv L s • p.field s

@[simp] theorem GlobalParallelField.sineTestField_zero_left
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀) (L : ℝ) :
    p.sineTestField L 0 = 0 := by
  rw [GlobalParallelField.sineTestField, sineTest_eq_zero_left, zero_smul]

@[simp] theorem GlobalParallelField.sineTestField_zero_right
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    {L : ℝ} (hL : 0 < L) :
    p.sineTestField L L = 0 := by
  rw [GlobalParallelField.sineTestField, sineTest_eq_zero_right L hL, zero_smul]

/-- The global sine field satisfies the genuine covariant product rule at
every time. -/
theorem GlobalParallelField.isCovariantAccelerationAt_sineTest
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (L t : ℝ) :
    CurveConnection.IsCovariantAccelerationAt cov (curve (shift γ t₀))
      (p.sineTestField L) t (velocity (shift γ t₀) t)
      (p.sineTestDerivativeField L t) := by
  change CurveConnection.IsCovariantAccelerationAt cov (curve (shift γ t₀))
    (fun s ↦ sineTest L s • p.field s) t (velocity (shift γ t₀) t)
    (sineTestDeriv L t • p.field t)
  exact p.isCovariantAccelerationAt_smul (sineTest L) (sineTestDeriv L)
    (fun s ↦ hasDerivAt_sineTest L s) t

/-- The squared norm of a sine field is the scalar sine square times the
squared norm of its initial tangent. -/
theorem GlobalParallelField.inner_sineTestField_self
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent) (L s : ℝ) :
    inner ℝ (p.sineTestField L s) (p.sineTestField L s) =
      sineTest L s ^ 2 * inner ℝ w₀ w₀ := by
  change inner ℝ (sineTest L s • p.field s) (sineTest L s • p.field s) = _
  rw [real_inner_smul_left, real_inner_smul_right,
    p.inner_eq_initial p hmetric s,
    p.inner_zero_eq_initialVectors p]
  ring

/-- The squared norm of the displayed covariant derivative is the scalar
derivative square times the squared norm of the initial tangent. -/
theorem GlobalParallelField.inner_sineTestDerivativeField_self
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent) (L s : ℝ) :
    inner ℝ (p.sineTestDerivativeField L s)
        (p.sineTestDerivativeField L s) =
      sineTestDeriv L s ^ 2 * inner ℝ w₀ w₀ := by
  change inner ℝ (sineTestDeriv L s • p.field s)
    (sineTestDeriv L s • p.field s) = _
  rw [real_inner_smul_left, real_inner_smul_right,
    p.inner_eq_initial p hmetric s,
    p.inner_zero_eq_initialVectors p]
  ring

/-- A global parallel field that starts transverse to the velocity remains
transverse after multiplication by the sine test. -/
theorem GlobalParallelField.inner_sineTestField_velocity_eq_zero
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (htransverse : inner ℝ w₀ (velocity γ t₀) = 0)
    (L s : ℝ) :
    inner ℝ (p.sineTestField L s) (velocity (shift γ t₀) s) = 0 := by
  obtain ⟨q, hq⟩ := exists_velocityGlobalParallelField
    (I := I) (M := M) γ t₀ hmetric
  change inner ℝ (sineTest L s • p.field s) (velocity (shift γ t₀) s) = 0
  rw [real_inner_smul_left, ← hq s]
  have hinner : inner ℝ (p.field s) (q.field s) =
      inner ℝ w₀ (velocity γ t₀) := by
    calc
      inner ℝ (p.field s) (q.field s) =
          inner ℝ (p.field 0) (q.field 0) :=
        p.inner_eq_initial q hmetric s
      _ = inner ℝ w₀ (velocity γ t₀) :=
        p.inner_zero_eq_initialVectors q
  rw [hinner, htransverse, mul_zero]

/-! ### The geometric index-form integrand -/

/-- The curvature scalar sampled by one global parallel field along a
geodesic.  It has the convention used by the Ricci trace in the public
statement: the parallel field occupies the first curvature slot and the
velocity occupies the final two slots. -/
def GlobalParallelField.curvatureCoefficient
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀) (s : ℝ) : ℝ :=
  inner ℝ (p.field s)
    (R (curve (shift γ t₀) s) (p.field s)
      (velocity (shift γ t₀) s) (velocity (shift γ t₀) s))

/-- The index form written directly for tangent-bundle-valued fields along a
fixed global geodesic.  It is deliberately a definition rather than an
assertion of nonnegativity: the latter is the still-open second-variation
bridge from endpoint minimization. -/
def globalIndexForm
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t₀ : ℝ)
    (J DJ : ∀ s : ℝ, TM (curve (shift γ t₀) s)) (L : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..L, inner ℝ (DJ s) (DJ s)) -
    (∫ s in (0 : ℝ)..L, inner ℝ (J s)
      (R (curve (shift γ t₀) s) (J s)
        (velocity (shift γ t₀) s) (velocity (shift γ t₀) s)))

/-- The curvature integrand of a sine-scaled parallel field factors into the
scalar sine square and the curvature coefficient of its underlying parallel
field. -/
theorem GlobalParallelField.inner_sineTestField_curvature
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (L s : ℝ) :
    inner ℝ (p.sineTestField L s)
      (R (curve (shift γ t₀) s) (p.sineTestField L s)
        (velocity (shift γ t₀) s) (velocity (shift γ t₀) s)) =
      sineTest L s ^ 2 * p.curvatureCoefficient R s := by
  change inner ℝ (sineTest L s • p.field s)
    (R (curve (shift γ t₀) s) (sineTest L s • p.field s)
      (velocity (shift γ t₀) s) (velocity (shift γ t₀) s)) = _
  simp only [map_smul, smul_apply,
    real_inner_smul_left, real_inner_smul_right]
  simp only [GlobalParallelField.curvatureCoefficient]
  ring

/-- For a unit initial tangent, the kinetic integral of the geometric sine
test is exactly the scalar kinetic integral. -/
theorem GlobalParallelField.intervalIntegral_inner_sineTestDerivativeField_self
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent) (hunit : ‖w₀‖ = 1) (L : ℝ) :
    (∫ s in (0 : ℝ)..L,
      inner ℝ (p.sineTestDerivativeField L s)
        (p.sineTestDerivativeField L s)) =
      ∫ s in (0 : ℝ)..L, sineTestDeriv L s ^ 2 := by
  have hself : inner ℝ w₀ w₀ = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit]
    norm_num
  apply intervalIntegral.integral_congr
  intro s hs
  change inner ℝ (p.sineTestDerivativeField L s)
    (p.sineTestDerivativeField L s) = sineTestDeriv L s ^ 2
  rw [p.inner_sineTestDerivativeField_self hmetric L s, hself, mul_one]

/-- For a unit initial tangent, the norm term of the geometric sine test is
exactly the scalar sine-square integrand. -/
theorem GlobalParallelField.intervalIntegral_inner_sineTestField_self
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent) (hunit : ‖w₀‖ = 1) (L : ℝ) :
    (∫ s in (0 : ℝ)..L,
      inner ℝ (p.sineTestField L s) (p.sineTestField L s)) =
      ∫ s in (0 : ℝ)..L, sineTest L s ^ 2 := by
  have hself : inner ℝ w₀ w₀ = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit]
    norm_num
  apply intervalIntegral.integral_congr
  intro s hs
  change inner ℝ (p.sineTestField L s) (p.sineTestField L s) =
    sineTest L s ^ 2
  rw [p.inner_sineTestField_self hmetric L s, hself, mul_one]

/-- The curvature integral of the geometric sine test is its scalar
sine-square weighting of the actual moving curvature coefficient. -/
theorem GlobalParallelField.intervalIntegral_inner_sineTestField_curvature
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀) (L : ℝ) :
    (∫ s in (0 : ℝ)..L,
      inner ℝ (p.sineTestField L s)
        (R (curve (shift γ t₀) s) (p.sineTestField L s)
          (velocity (shift γ t₀) s) (velocity (shift γ t₀) s))) =
      ∫ s in (0 : ℝ)..L, sineTest L s ^ 2 * p.curvatureCoefficient R s := by
  apply intervalIntegral.integral_congr
  intro s hs
  exact p.inner_sineTestField_curvature R L s

/-- The genuine tangent-bundle index form of a unit sine test reduces to the
scalar kinetic integral minus the actual scalar curvature coefficient. -/
theorem globalIndexForm_sineTest_eq
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent) (hunit : ‖w₀‖ = 1) (L : ℝ) :
    globalIndexForm R γ t₀ (p.sineTestField L)
      (p.sineTestDerivativeField L) L =
      (∫ s in (0 : ℝ)..L, sineTestDeriv L s ^ 2) -
        (∫ s in (0 : ℝ)..L, sineTest L s ^ 2 * p.curvatureCoefficient R s) := by
  unfold globalIndexForm
  rw [p.intervalIntegral_inner_sineTestDerivativeField_self hmetric hunit L,
    p.intervalIntegral_inner_sineTestField_curvature R L]

end IntrinsicGeodesic.GlobalGeodesic

end BonnetMyersEntry
