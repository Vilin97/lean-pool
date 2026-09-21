/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib

/-!
# Independent geometric vocabulary for Lichnerowicz--Obata

Only Mathlib is imported. Curvature is the actual covariant-derivative
commutator, Ricci is its orthonormal trace, and the scalar Laplacian is the
trace of the covariant derivative of the Riesz gradient. The round target
uses the standard sphere charts and its radius-scaled induced metric.

The smooth-extension construction is adapted from the independently stated
almost-Schur geometry at 3faf25aefc27842a77c37ca178e8a40a20bb20c7, which in turn
credits the contracted-Bianchi core; see PROVENANCE.md. No spectral, Bochner,
Hessian, geodesic, or sphere-identification bridge is assumed.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff BigOperators

namespace LichnerowiczObataEntry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "n" => (Module.finrank ℝ E)

local instance finiteTangent (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- Choose a smooth cutoff supported in the tangent trivialization. -/
def extensionBump (x : M) : SmoothBumpFunction I x := by
  let t := trivializationAt E TM x
  have ht : t.baseSet ∈ nhds x :=
    t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E TM x)
  have hφ : ∃ φ : SmoothBumpFunction I x, True ∧ tsupport φ ⊆ t.baseSet :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (c := x)).mem_iff.mp ht
  exact Classical.choose hφ

/-- Extend a tangent vector smoothly without changing it near its base point. -/
def extension (x : M) (v : TM x) : Π y : M, TM y :=
  ((extensionBump (I := I) x : M → ℝ) • FiberBundle.extend E v)

/-- R(X,Y)Z = ∇X∇YZ − ∇Y∇XZ − ∇[X,Y]Z, evaluated at x. -/
def curvature (cov : CovariantDerivative I E TM) (x : M) (u v w : TM x) : TM x :=
  let X := extension (I := I) x u
  let Y := extension (I := I) x v
  let Z := extension (I := I) x w
  cov (fun y => cov Z y (Y y)) x (X x) -
    cov (fun y => cov Z y (X y)) x (Y x) -
    cov Z x (VectorField.mlieBracket I X Y x)

/-- Ric(u,v) is the trace of w ↦ R(w,u)v. -/
def ricci (cov : CovariantDerivative I E TM) (x : M) (u v : TM x) : ℝ :=
  let b := stdOrthonormalBasis ℝ (TM x)
  ∑ i, inner ℝ (curvature cov x (b i) u v) (b i)

/-- The actual metric Riesz representative of the manifold differential. -/
def gradient (f : M → ℝ) (x : M) : TM x :=
  (InnerProductSpace.toDual ℝ (TM x)).symm (mvfderiv (I := I) f x)

/-- The div-grad Laplace--Beltrami operator of the supplied connection. -/
def laplacian (cov : CovariantDerivative I E TM) (f : M → ℝ) (x : M) : ℝ :=
  LinearMap.trace ℝ (TM x) (cov (gradient (I := I) f) x).toLinearMap

/-- Attainment and minimality among positive smooth eigenvalues. -/
def isFirstPositiveEigenvalue (cov : CovariantDerivative I E TM) (μ : ℝ) : Prop :=
  0 < μ ∧
    (∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ (∃ x y, f x ≠ f y) ∧
      ∀ x, laplacian cov f x = -μ * f x) ∧
    ∀ s : ℝ, 0 < s →
      (∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ (∃ x y, f x ≠ f y) ∧
        ∀ x, laplacian cov f x = -s * f x) → μ ≤ s

/-- Smooth Riemannian isometry to the round sphere of radius 1/sqrt K,
expressed by the exact radius-scaled induced metric in standard sphere charts. -/
def isRoundSphere (K : ℝ) : Prop :=
  ∃ d : M ≃ₘ⟮I, 𝓡 n⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
    ∀ (x : M) (v w : TM x),
      inner ℝ
        (mvfderiv I (fun y : M => (1 / Real.sqrt K) •
          (d y : EuclideanSpace ℝ (Fin (n + 1)))) x v)
        (mvfderiv I (fun y : M => (1 / Real.sqrt K) •
          (d y : EuclideanSpace ℝ (Fin (n + 1)))) x w) = inner ℝ v w

variable [Nonempty M] [LindelofSpace M] [CompactSpace M] [PreconnectedSpace M]

/-- Construct the Levi-Civita connection, then prove attainment, the sharp
eigenvalue bound, and the complete round-sphere equality characterization. -/
def geometricStatement : Prop :=
  ∃ cov : CovariantDerivative I E TM,
    (@CovariantDerivative.IsMetricCompatible E _ _ H _ I M _ _ E _ _ TM _
      (fun _ => inferInstance) (fun _ => inferInstance) _ cov _ _ _ _) ∧
    cov.torsion = 0 ∧ Nonempty (cov.ContMDiffCovariantDerivative 1) ∧
    ∀ (K : ℝ), 0 < K → 2 ≤ n →
      (∀ (x : M) (v : TM x), ((n : ℝ) - 1) * K * ‖v‖ ^ 2 ≤ ricci cov x v v) →
      ∃ μ : ℝ, isFirstPositiveEigenvalue cov μ ∧ (n : ℝ) * K ≤ μ ∧
        (μ = (n : ℝ) * K ↔ isRoundSphere (I := I) (M := M) K)

end LichnerowiczObataEntry.Geometry
