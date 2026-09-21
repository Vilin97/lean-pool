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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchiBridge
import LeanPool.PoincareGeometry.ContractedBianchiSections

/-!
# Double-contracted second Bianchi identity

The proof uses the candidate-local curvature development only on the Solution side.  The
Challenge-side definitions are repeated verbatim so the Comparator sees the same auditable
connection-derived surface without granting the Challenge access to candidate-local modules.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace ContractedBianchi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 2) M] [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M] [IsManifold I ((3 : ℕ∞) + 1) M]

noncomputable def along
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, TangentSpace I x) :
    Π x : M, TangentSpace I x :=
  fun x ↦ cov σ x (X x)

noncomputable def curvatureAux
    (X Y Z : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  along cov X (along cov Y Z) - along cov Y (along cov X Z) -
    along cov (VectorField.mlieBracket I X Y) Z

noncomputable def secondBianchiAux
    (X Y Z W : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  along cov X (curvatureAux cov Y Z W) -
    curvatureAux cov (along cov X Y) Z W -
    curvatureAux cov Y (along cov X Z) W -
    curvatureAux cov Y Z (along cov X W)

def IsMetricCompatibleTangent : Prop :=
  ∀ {x : M} {σ τ : Π x : M, TangentSpace I x},
    MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      ∀ u : TangentSpace I x,
        mvfderiv (I := I) (fun y ↦ inner ℝ (σ y) (τ y)) x u =
          inner ℝ (cov σ x u) (τ x) + inner ℝ (σ x) (cov τ x u)

noncomputable def curvatureCovariantDerivative
    (extension : ∀ x : M, TangentSpace I x → Π y : M, TangentSpace I y)
    (x : M) (p a b c : TangentSpace I x) : TangentSpace I x :=
  secondBianchiAux cov (extension x p) (extension x a) (extension x b) (extension x c) x

noncomputable def curvatureCovariantDerivativeInner
    (extension : ∀ x : M, TangentSpace I x → Π y : M, TangentSpace I y)
    (x : M) (p a b c d : TangentSpace I x) : ℝ :=
  inner ℝ (curvatureCovariantDerivative cov extension x p a b c) (extension x d x)

theorem contractedSecondBianchi
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (extension : ∀ x : M, TangentSpace I x → Π y : M, TangentSpace I y)
    (x : M) (hT : cov.torsion = 0)
    (hmetric : IsMetricCompatibleTangent cov)
    (hvalue : ∀ v : TangentSpace I x, extension x v x = v)
    (hext : ∀ v : TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (extension x v)))
    (b : OrthonormalBasis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ
      (TangentSpace I x))
    (w : TangentSpace I x) :
    (∑ i, ∑ k, curvatureCovariantDerivativeInner
      cov extension x w (b k) (b i) (b i) (b k)) =
    2 * ∑ i, ∑ k, curvatureCovariantDerivativeInner
      cov extension x (b i) (b k) (b i) w (b k) := by
  have hmetric' : cov.IsMetricCompatibleTangent := by
    intro x σ τ hσ hτ u
    exact hmetric hσ hτ u
  have h := CovariantDerivative.curvatureCovariantDerivativeInner_doubleContraction_sections
    cov x hT hmetric'
    (fun i ↦ extension x (b i)) (extension x w)
    (fun i ↦ hext (b i)) (hext w)
  change (∑ i, ∑ k, inner ℝ
      (CovariantDerivative.secondBianchiAux cov (extension x (w))
        (extension x (b k)) (extension x (b i)) (extension x (b i)) x)
      (extension x (b k) x)) =
    2 * ∑ i, ∑ k, inner ℝ
      (CovariantDerivative.secondBianchiAux cov (extension x (b i))
        (extension x (b k)) (extension x (b i)) (extension x w) x)
      (extension x (b k) x)
  exact h

end ContractedBianchi
