/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RaisedRicci
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TimeDependent
public import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.LeastEigenvalue

/-!
# Three-dimensional curvature spectrum along a metric family

This file lifts the intrinsic three-dimensional curvature spectrum to each
time slice of a time-dependent Riemannian metric and a Levi-Civita connection
family.  It supplies the geometric `lambda`, `mu`, and `nu` fields used by the
Hamilton--Ivey estimate.  Their ordering and scalar-curvature sum are inherited
from the self-adjoint spectral theorem and the actual curvature contractions.
-/

@[expose] public noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Evaluation of the actual Ricci-complement curvature endomorphism at a
time slice.  Packaging only its value avoids exposing the definitionally
distinct tangent-fibre norm instance used to construct the continuous linear
map. -/
def curvatureEndomorphismApply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) (x : M) (v : TM x) : TM x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  exact CovariantDerivative.ricciComplementEndomorphism (cov t) x v

/-- The ordered triple of actual curvature-operator eigenvalues at a spacetime
point, in the normalization where each is twice a sectional curvature. -/
def curvatureEigenvalues
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : Fin 3 → ℝ := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  exact CovariantDerivative.ricciComplementEigenvalues
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)

/-- Largest curvature-operator eigenvalue. -/
def curvatureLambda
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : ℝ :=
  g.curvatureEigenvalues cov hcov hLevi hdim t x 0

/-- Middle curvature-operator eigenvalue. -/
def curvatureMu
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : ℝ :=
  g.curvatureEigenvalues cov hcov hLevi hdim t x 1

/-- Least curvature-operator eigenvalue. -/
def curvatureNu
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : ℝ :=
  g.curvatureEigenvalues cov hcov hLevi hdim t x 2

/-! Evaluation of the genuine orthonormal curvature eigenframe corresponding
to `curvatureEigenvalues`.  The frame itself remains local to the definition
so that the public API does not expose a choice-dependent fibrewise instance. -/

def curvatureEigenbasisVector
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) (i : Fin 3) : TM x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  exact CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) i

/-- A unit eigenvector for the least curvature eigenvalue at a spacetime
point.  This is the contact vector used by the tensor maximum principle. -/
def curvatureNuEigenvector
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : TM x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  exact CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2

@[simp] theorem inner_curvatureNuEigenvector_self
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    (g t).inner x
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x)
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x) = 1 := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  change Inner.inner ℝ
      ((CovariantDerivative.ricciComplementEigenbasis
        (I := I) (M := M) (E := E)
        (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)) 2)
      ((CovariantDerivative.ricciComplementEigenbasis
        (I := I) (M := M) (E := E)
        (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)) 2) = 1
  simpa using (CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)).orthonormal
      (i := (2 : Fin 3)) (j := (2 : Fin 3))

/-- The selected least eigenvector realizes the least curvature eigenvalue
as the quadratic form of the actual Ricci-complement endomorphism. -/
theorem curvatureNu_eq_inner_ricciComplement_eigenvector
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    g.curvatureNu cov hcov hLevi hdim t x =
      (g t).inner x
        (g.curvatureEndomorphismApply cov hcov t x
          (g.curvatureNuEigenvector cov hcov hLevi hdim t x))
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  change CovariantDerivative.ricciComplementEigenvalues
      (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2 = Inner.inner ℝ
    (CovariantDerivative.ricciComplementEndomorphism (cov t) x
      (CovariantDerivative.ricciComplementEigenbasis
        (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2))
    (CovariantDerivative.ricciComplementEigenbasis
      (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2)
  let b := CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)
  have happ := CovariantDerivative.ricciComplementEndomorphism_apply_eigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2
  have hinner := congrArg (fun z : TM x => Inner.inner ℝ z (b 2)) happ
  simpa [b, real_inner_smul_left] using hinner.symm

/-- The selected least-curvature vector satisfies the full eigenvector
equation, not merely the corresponding Rayleigh-quotient identity. -/
theorem curvatureEndomorphismApply_curvatureNuEigenvector
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    g.curvatureEndomorphismApply cov hcov t x
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x) =
      g.curvatureNu cov hcov hLevi hdim t x •
        g.curvatureNuEigenvector cov hcov hLevi hdim t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  change CovariantDerivative.ricciComplementEndomorphism (cov t) x
      (CovariantDerivative.ricciComplementEigenbasis
        (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2) =
    CovariantDerivative.ricciComplementEigenvalues
      (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2 •
      CovariantDerivative.ricciComplementEigenbasis
        (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2
  exact CovariantDerivative.ricciComplementEndomorphism_apply_eigenbasis
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2

/-! The spectrum is tied back to the original curvature tensor: the least
curvature-operator eigenvalue is twice the sectional-curvature numerator of
the complementary eigenplane.  This is the dimension-three algebraic bridge
behind the normalization used by the Hamilton--Ivey reaction. -/

theorem curvatureNu_eq_two_sectionalCurvatureNumerator_complement
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    (letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
     letI : ContMDiffCovariantDerivative
       (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
     g.curvatureNu cov hcov hLevi hdim t x =
       2 * CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x
         ((CovariantDerivative.ricciComplementEigenbasis
           (I := I) (M := M) (E := E)
           (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)) 0)
         ((CovariantDerivative.ricciComplementEigenbasis
           (I := I) (M := M) (E := E)
           (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)) 1)) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  let b := CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)
  have heig := CovariantDerivative.ricciComplementEndomorphism_apply_eigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2
  have hinner := congrArg (fun z : TM x => Inner.inner ℝ z (b 2)) heig
  have hsection := CovariantDerivative.inner_ricciComplementEndomorphism_basis_two_finrank_three
    (I := I) (M := M) (E := E) (cov t) (hLevi t).2 x b
  change CovariantDerivative.ricciComplementEigenvalues
      (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2 = _
  have hnorm : Inner.inner ℝ (b 2) (b 2) = 1 := by
    simpa using b.orthonormal (i := (2 : Fin 3)) (j := (2 : Fin 3))
  have hinner' :
      Inner.inner ℝ
          (CovariantDerivative.ricciComplementEndomorphism (cov t) x (b 2)) (b 2) =
        CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2 := by
    calc
      Inner.inner ℝ
          (CovariantDerivative.ricciComplementEndomorphism (cov t) x (b 2)) (b 2) =
          Inner.inner ℝ
            (CovariantDerivative.ricciComplementEigenvalues
              (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2 • b 2) (b 2) := hinner
      _ = CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2 := by
        rw [real_inner_smul_left, hnorm, mul_one]
  have hmain :
      CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2 =
        2 * CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x (b 0) (b 1) := by
    calc
      CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2 =
          Inner.inner ℝ
            (CovariantDerivative.ricciComplementEndomorphism (cov t) x (b 2)) (b 2) :=
        hinner'.symm
      _ = 2 * CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x (b 0) (b 1) :=
        hsection
  simpa [b] using hmain

theorem curvatureLambda_eq_two_sectionalCurvatureNumerator_complement
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    (letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
     letI : ContMDiffCovariantDerivative
       (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
     g.curvatureLambda cov hcov hLevi hdim t x =
       2 * CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x
         ((CovariantDerivative.ricciComplementEigenbasis
           (I := I) (M := M) (E := E)
           (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)) 1)
         ((CovariantDerivative.ricciComplementEigenbasis
           (I := I) (M := M) (E := E)
           (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)) 2)) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  let b := CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)
  have heig := CovariantDerivative.ricciComplementEndomorphism_apply_eigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 0
  have hinner := congrArg (fun z : TM x => Inner.inner ℝ z (b 0)) heig
  have hsection := CovariantDerivative.inner_ricciComplementEndomorphism_basis_zero_finrank_three
    (I := I) (M := M) (E := E) (cov t) (hLevi t).2 x b
  change CovariantDerivative.ricciComplementEigenvalues
      (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 0 = _
  have hnorm : Inner.inner ℝ (b 0) (b 0) = 1 := by
    simpa using b.orthonormal (i := (0 : Fin 3)) (j := (0 : Fin 3))
  have hinner' :
      Inner.inner ℝ
          (CovariantDerivative.ricciComplementEndomorphism (cov t) x (b 0)) (b 0) =
        CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 0 := by
    calc
      Inner.inner ℝ
          (CovariantDerivative.ricciComplementEndomorphism (cov t) x (b 0)) (b 0) =
          Inner.inner ℝ
            (CovariantDerivative.ricciComplementEigenvalues
              (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 0 • b 0) (b 0) := hinner
      _ = CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 0 := by
        rw [real_inner_smul_left, hnorm, mul_one]
  have hmain :
      CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 0 =
        2 * CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x (b 1) (b 2) := by
    calc
      CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 0 =
          Inner.inner ℝ
            (CovariantDerivative.ricciComplementEndomorphism (cov t) x (b 0)) (b 0) :=
        hinner'.symm
      _ = 2 * CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x (b 1) (b 2) :=
        hsection
  simpa [b] using hmain

theorem curvatureMu_eq_two_sectionalCurvatureNumerator_complement
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    (letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
     letI : ContMDiffCovariantDerivative
       (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
     g.curvatureMu cov hcov hLevi hdim t x =
       2 * CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x
         ((CovariantDerivative.ricciComplementEigenbasis
           (I := I) (M := M) (E := E)
           (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)) 0)
         ((CovariantDerivative.ricciComplementEigenbasis
           (I := I) (M := M) (E := E)
           (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)) 2)) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  let b := CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)
  have heig := CovariantDerivative.ricciComplementEndomorphism_apply_eigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 1
  have hinner := congrArg (fun z : TM x => Inner.inner ℝ z (b 1)) heig
  have hsection := CovariantDerivative.inner_ricciComplementEndomorphism_basis_one_finrank_three
    (I := I) (M := M) (E := E) (cov t) (hLevi t).2 x b
  change CovariantDerivative.ricciComplementEigenvalues
      (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 1 = _
  have hnorm : Inner.inner ℝ (b 1) (b 1) = 1 := by
    simpa using b.orthonormal (i := (1 : Fin 3)) (j := (1 : Fin 3))
  have hinner' :
      Inner.inner ℝ
          (CovariantDerivative.ricciComplementEndomorphism (cov t) x (b 1)) (b 1) =
        CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 1 := by
    calc
      Inner.inner ℝ
          (CovariantDerivative.ricciComplementEndomorphism (cov t) x (b 1)) (b 1) =
          Inner.inner ℝ
            (CovariantDerivative.ricciComplementEigenvalues
              (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 1 • b 1) (b 1) := hinner
      _ = CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 1 := by
        rw [real_inner_smul_left, hnorm, mul_one]
  have hmain :
      CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 1 =
        2 * CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x (b 0) (b 2) := by
    calc
      CovariantDerivative.ricciComplementEigenvalues
          (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 1 =
          Inner.inner ℝ
            (CovariantDerivative.ricciComplementEndomorphism (cov t) x (b 1)) (b 1) :=
        hinner'.symm
      _ = 2 * CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x (b 0) (b 2) :=
        hsection
  simpa [b] using hmain

/-- Every unit vector gives an upper support for the least genuine curvature
eigenvalue. -/
theorem curvatureNu_le_inner_ricciComplement_of_norm_eq_one
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) {v : TM x} (hv : (g t).inner x v v = 1) :
    g.curvatureNu cov hcov hLevi hdim t x ≤
      (g t).inner x v
        (g.curvatureEndomorphismApply cov hcov t x v) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  change g.curvatureNu cov hcov hLevi hdim t x ≤ Inner.inner ℝ v
    (CovariantDerivative.ricciComplementEndomorphism (cov t) x v)
  have hvnorm : ‖v‖ = 1 := by
    have hnormsq := real_inner_self_eq_norm_sq v
    change Inner.inner ℝ v v = 1 at hv
    nlinarith [norm_nonneg v]
  exact (CovariantDerivative.ricciComplementEndomorphism_isSymmetric
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x).eigenvalue_two_le_inner_apply_of_norm_eq_one
      (hdim x) hvnorm

/-- Homogeneous geometric Rayleigh support for the least curvature
eigenvalue.  This is the form used for a smooth local extension of a contact
eigenvector: the extension need not remain normalized away from the contact
point. -/
theorem curvatureNu_mul_inner_self_le_inner_ricciComplement
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) (v : TM x) :
    g.curvatureNu cov hcov hLevi hdim t x * (g t).inner x v v ≤
      (g t).inner x v (g.curvatureEndomorphismApply cov hcov t x v) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  change CovariantDerivative.ricciComplementEigenvalues
      (cov t) (hLevi t).1 (hLevi t).2 x (hdim x) 2 * Inner.inner ℝ v v ≤
    Inner.inner ℝ v
      (CovariantDerivative.ricciComplementEndomorphism (cov t) x v)
  rw [real_inner_self_eq_norm_sq]
  exact (CovariantDerivative.ricciComplementEndomorphism_isSymmetric
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x).eigenvalue_two_mul_norm_sq_le_inner_apply
      (hdim x) v

/-- The Rayleigh quotient of the actual Ricci-complement curvature
endomorphism at a time slice. -/
def curvatureRayleighQuotient
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) (x : M) (v : TM x) : ℝ :=
  (g t).inner x v (g.curvatureEndomorphismApply cov hcov t x v) /
    (g t).inner x v v

/-- The geometric least curvature eigenvalue lies below every defined
Rayleigh quotient. -/
theorem curvatureNu_le_curvatureRayleighQuotient
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) {v : TM x} (hv : 0 < (g t).inner x v v) :
    g.curvatureNu cov hcov hLevi hdim t x ≤
      g.curvatureRayleighQuotient cov hcov t x v := by
  rw [curvatureRayleighQuotient, le_div_iff₀ hv]
  exact g.curvatureNu_mul_inner_self_le_inner_ricciComplement
    cov hcov hLevi hdim t x v

/-- At the selected least eigenvector, the Rayleigh support touches the
least curvature eigenvalue exactly. -/
theorem curvatureRayleighQuotient_curvatureNuEigenvector
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    g.curvatureRayleighQuotient cov hcov t x
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x) =
      g.curvatureNu cov hcov hLevi hdim t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  rw [curvatureRayleighQuotient,
    g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t x, div_one]
  rw [show (g t).inner x
      (g.curvatureNuEigenvector cov hcov hLevi hdim t x)
      (g.curvatureEndomorphismApply cov hcov t x
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x)) =
      (g t).inner x
      (g.curvatureEndomorphismApply cov hcov t x
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x))
      (g.curvatureNuEigenvector cov hcov hLevi hdim t x) by
        exact real_inner_comm
          (g.curvatureEndomorphismApply cov hcov t x
            (g.curvatureNuEigenvector cov hcov hLevi hdim t x))
          (g.curvatureNuEigenvector cov hcov hLevi hdim t x)]
  exact (g.curvatureNu_eq_inner_ricciComplement_eigenvector
    cov hcov hLevi hdim t x).symm

/-- Spatial Rayleigh support obtained by smoothly extending the least
curvature eigenvector from a chosen contact point. -/
def curvatureNuSpatialSupport
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x₀ y : M) : ℝ :=
  g.curvatureRayleighQuotient cov hcov t y
    (smoothExtend (I := I) (F := E) (V := TM) x₀
      (g.curvatureNuEigenvector cov hcov hLevi hdim t x₀) y)

/-- The spatial Rayleigh support touches the least curvature eigenvalue at
its base point. -/
theorem curvatureNuSpatialSupport_eq_at_base
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x₀ : M) :
    g.curvatureNuSpatialSupport cov hcov hLevi hdim t x₀ x₀ =
      g.curvatureNu cov hcov hLevi hdim t x₀ := by
  rw [curvatureNuSpatialSupport, smoothExtend_apply]
  exact g.curvatureRayleighQuotient_curvatureNuEigenvector
    cov hcov hLevi hdim t x₀

/-- Near the contact point, the smoothly extended eigenvector has positive
metric square and its Rayleigh quotient is an upper support for the least
curvature eigenvalue. -/
theorem curvatureNu_le_spatialSupport_eventually
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x₀ : M) :
    ∀ᶠ y in nhds x₀,
      g.curvatureNu cov hcov hLevi hdim t y ≤
        g.curvatureNuSpatialSupport cov hcov hLevi hdim t x₀ y := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let V : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x₀
      (g.curvatureNuEigenvector cov hcov hLevi hdim t x₀)
  have hV : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% V) := by
    simpa [V] using smoothExtend_contMDiff_one
      (I := I) (F := E) (V := TM) x₀
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x₀)
  have hinner : ContMDiff I 𝓘(ℝ) 1
      (fun y => Inner.inner ℝ (V y) (V y)) :=
    ContMDiff.inner_bundle (IM := I) (IB := I) (F := E) (E := TM) hV hV
  have hbase : Inner.inner ℝ (V x₀) (V x₀) = 1 := by
    dsimp only [V]
    rw [smoothExtend_apply]
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t x₀
  have hevent : ∀ᶠ y in nhds x₀, 0 < Inner.inner ℝ (V y) (V y) := by
    have hopen : IsOpen {r : ℝ | 0 < r} := isOpen_Ioi
    have hmem : Inner.inner ℝ (V x₀) (V x₀) ∈ {r : ℝ | 0 < r} := by
      rw [hbase]
      norm_num
    exact hinner.continuous.continuousAt (hopen.mem_nhds hmem)
  filter_upwards [hevent] with y hy
  exact g.curvatureNu_le_curvatureRayleighQuotient cov hcov hLevi hdim t y hy

/-- The three curvature eigenvalues are decreasingly ordered at every
spacetime point. -/
theorem curvatureEigenvalues_antitone
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    Antitone (g.curvatureEigenvalues cov hcov hLevi hdim t x) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  exact CovariantDerivative.ricciComplementEigenvalues_antitone
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)

theorem curvatureLambda_ge_mu
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    g.curvatureMu cov hcov hLevi hdim t x ≤
      g.curvatureLambda cov hcov hLevi hdim t x :=
  g.curvatureEigenvalues_antitone cov hcov hLevi hdim t x (by decide)

theorem curvatureMu_ge_nu
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    g.curvatureNu cov hcov hLevi hdim t x ≤
      g.curvatureMu cov hcov hLevi hdim t x :=
  g.curvatureEigenvalues_antitone cov hcov hLevi hdim t x (by decide)

/-- The geometric scalar curvature equals `lambda + mu + nu` at every
spacetime point. -/
theorem curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    g.curvatureLambda cov hcov hLevi hdim t x +
        g.curvatureMu cov hcov hLevi hdim t x +
        g.curvatureNu cov hcov hLevi hdim t x =
      g.scalarCurvature cov hcov t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  exact CovariantDerivative.threeDimensionalCurvatureLambda_add_mu_add_nu_eq_scalarCurvature
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)

end CovariantDerivative.TimeDependentRiemannianMetric
