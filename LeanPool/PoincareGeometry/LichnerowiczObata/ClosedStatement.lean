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

public import Mathlib

/-!
# Complete, independently auditable Lichnerowicz--Obata statement

This is the same geometric theorem as the parameterized statement. All manifold
parameters and all nine geometric definitions are explicitly inside one closed
proposition, so the registry can print its signature without reconstructing
Mathlib's dependent types as opaque axioms. Comparator compares this entire
definition body, not an alias to unchecked project definitions.

The scalar operator is div-grad; the Ricci bound is (n-1)*K, K > 0; the first
positive smooth eigenvalue is attained, is at least n*K, and equals n*K exactly
for the round sphere of radius 1/sqrt K. No geometric or analytic bridge is
assumed. The formal equivalence with the original statement is proved in
StatementEquivalence.lean. The smooth-extension construction is inherited from
the independently stated geometry at 3faf25aefc27842a77c37ca178e8a40a20bb20c7;
see PROVENANCE.md for its contracted-Bianchi and almost-Schur attribution.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff BigOperators

namespace LichnerowiczObataEntry.Geometry

universe u v w

/-- The full quantified geometric statement, with every geometric definition
explicitly included in the body selected for independent comparison. -/
def completeStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
    [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
    [Nonempty M] [LindelofSpace M] [CompactSpace M] [PreconnectedSpace M],
  let TM := (TangentSpace I : M → Type _)
  let n := Module.finrank ℝ E
  letI : (x : M) → FiniteDimensional ℝ (TM x) :=
    fun x => VectorBundle.finiteDimensional ℝ E TM x
  -- Smooth cutoff and tangent extension.
  let extensionBump (x : M) : SmoothBumpFunction I x := by
    let t := trivializationAt E TM x
    have ht : t.baseSet ∈ nhds x :=
      t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E TM x)
    have hφ : ∃ φ : SmoothBumpFunction I x, True ∧ tsupport φ ⊆ t.baseSet :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := I) (c := x)).mem_iff.mp ht
    exact Classical.choose hφ
  let extension (x : M) (a : TM x) : Π y : M, TM y :=
    ((extensionBump x : M → ℝ) • FiberBundle.extend E a)
  -- Actual covariant-derivative commutator and orthonormal Ricci trace.
  let curvature (cov : CovariantDerivative I E TM) (x : M) (a b c : TM x) : TM x :=
    let X := extension x a
    let Y := extension x b
    let Z := extension x c
    cov (fun y => cov Z y (Y y)) x (X x) -
      cov (fun y => cov Z y (X y)) x (Y x) -
      cov Z x (VectorField.mlieBracket I X Y x)
  let ricci (cov : CovariantDerivative I E TM) (x : M) (a b : TM x) : ℝ :=
    let basis := stdOrthonormalBasis ℝ (TM x)
    ∑ i, inner ℝ (curvature cov x (basis i) a b) (basis i)
  -- Metric Riesz gradient and div-grad Laplace--Beltrami operator.
  let gradient (f : M → ℝ) (x : M) : TM x :=
    (InnerProductSpace.toDual ℝ (TM x)).symm (mvfderiv (I := I) f x)
  let laplacian (cov : CovariantDerivative I E TM) (f : M → ℝ) (x : M) : ℝ :=
    LinearMap.trace ℝ (TM x) (cov (gradient f) x).toLinearMap
  -- Attainment, nonconstancy, and minimality among positive smooth eigenvalues.
  let isFirstPositiveEigenvalue (cov : CovariantDerivative I E TM) (μ : ℝ) : Prop :=
    0 < μ ∧
      (∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ (∃ x y, f x ≠ f y) ∧
        ∀ x, laplacian cov f x = -μ * f x) ∧
      ∀ s : ℝ, 0 < s →
        (∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ (∃ x y, f x ≠ f y) ∧
          ∀ x, laplacian cov f x = -s * f x) → μ ≤ s
  -- Smooth isometry to the radius-scaled standard sphere, not just homeomorphism.
  let isRoundSphere (K : ℝ) : Prop :=
    ∃ d : M ≃ₘ⟮I, 𝓡 n⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      ∀ (x : M) (a b : TM x),
        inner ℝ
          (mvfderiv I (fun y : M => (1 / Real.sqrt K) •
            (d y : EuclideanSpace ℝ (Fin (n + 1)))) x a)
          (mvfderiv I (fun y : M => (1 / Real.sqrt K) •
            (d y : EuclideanSpace ℝ (Fin (n + 1)))) x b) = inner ℝ a b
  -- Construct the Levi-Civita connection; prove the bound and both equality directions.
  ∃ cov : CovariantDerivative I E TM,
    (@CovariantDerivative.IsMetricCompatible E _ _ H _ I M _ _ E _ _ TM _
      (fun _ => inferInstance) (fun _ => inferInstance) _ cov _ _ _ _) ∧
    cov.torsion = 0 ∧ Nonempty (cov.ContMDiffCovariantDerivative 1) ∧
    ∀ (K : ℝ), 0 < K → 2 ≤ n →
      (∀ (x : M) (a : TM x), ((n : ℝ) - 1) * K * ‖a‖ ^ 2 ≤ ricci cov x a a) →
      ∃ μ : ℝ, isFirstPositiveEigenvalue cov μ ∧ (n : ℝ) * K ≤ μ ∧
        (μ = (n : ℝ) * K ↔ isRoundSphere K)

end LichnerowiczObataEntry.Geometry
