/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSection
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Levi-Civita connections

This file introduces torsion-free and Levi-Civita predicates for affine connections on the tangent
bundle of a Riemannian manifold, proves uniqueness, and constructs Levi-Civita connections from an
arbitrary affine connection by the standard correction formula.

The main result is the expected uniqueness statement at the current mathlib boundary:
if two affine connections are both torsion-free and metric-compatible, then their difference
one-form vanishes.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Bundle Manifold ContDiff

variable {E : Type*} [hREGroup : NormedAddCommGroup E] [hRESpace : NormedSpace ℝ E]
  {H : Type*} [hRHTop : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [hRMTop : TopologicalSpace M] [hRCharted : ChartedSpace H M]
  [hRFinite : FiniteDimensional ℝ E] [hRComplete : CompleteSpace E]
  [hRManifold : IsManifold I 2 M]
  [hRRiemannian : RiemannianBundle (TangentSpace I : M → Type _)]
  [hRSmooth : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TStar" => (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
local notation "TEnd" => (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
local notation "TCorr" =>
  (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)

noncomputable instance tangentSpaceFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x

namespace ContMDiffWithinAt

/-- A `C^1` tangent-vector field yields a `C^1` cotangent-field section via the Riemannian metric. -/
theorem toDualSection
    {σ : ∀ x, TM x} {s : Set M} {x₀ : M}
    (hσ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (σ x)) s x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (InnerProductSpace.toDual ℝ (TM x) (σ x))) s x₀ := by
  rcases (show IsContMDiffRiemannianBundle I 1 E TM from inferInstance).exists_contMDiff with
    ⟨g, hg, hinner⟩
  have happly : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (g x (σ x))) s x₀ := by
    exact (hg x₀).contMDiffWithinAt.clm_bundle_apply hσ
  have hEq :
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (g x (σ x))) =
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (InnerProductSpace.toDual ℝ (TM x) (σ x))) := by
    funext x
    refine congrArg (fun φ ↦ TotalSpace.mk' (E := TStar) (E →L[ℝ] ℝ) x φ) ?_
    ext u
    simp [hinner]
  rw [hEq] at happly
  exact happly

end ContMDiffWithinAt

namespace ContMDiffAt

theorem toDualSection
    {σ : ∀ x, TM x} {x₀ : M}
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (σ x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (InnerProductSpace.toDual ℝ (TM x) (σ x))) x₀ := by
  exact ContMDiffWithinAt.toDualSection (I := I) (E := E) (s := Set.univ) hσ

end ContMDiffAt

namespace ContMDiffOn

theorem toDualSection
    {σ : ∀ x, TM x} {s : Set M}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (σ x)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (InnerProductSpace.toDual ℝ (TM x) (σ x))) s := by
  intro x hx
  exact (hσ x hx).toDualSection (I := I) (E := E)

end ContMDiffOn

namespace ContMDiff

theorem toDualSection
    {σ : ∀ x, TM x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (σ x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (InnerProductSpace.toDual ℝ (TM x) (σ x))) := by
  intro x
  exact (hσ x).toDualSection (I := I) (E := E)

end ContMDiff

namespace ContinuousLinearMap

lemma inCoordinates_comp_eq
    {x₀ x : M} {φ : TM x →L[ℝ] ℝ} {A : TM x →L[ℝ] TM x}
    (hxT : x ∈ (trivializationAt E TM x₀).baseSet) :
    ContinuousLinearMap.inCoordinates E TM ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x (φ.comp A) =
      (ContinuousLinearMap.inCoordinates E TM ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x φ).comp
        (ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x A) := by
  let e := trivializationAt E TM x₀
  let ex := e.continuousLinearEquivAt ℝ x hxT
  ext u
  have hleft :
      ContinuousLinearMap.inCoordinates E TM ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x (φ.comp A) u =
        (φ.comp A) (ex.symm u) := by
    simpa [e, ex, ContinuousLinearMap.comp_apply] using
      congrArg (fun L : E →L[ℝ] ℝ => L u)
        (ContinuousLinearMap.inCoordinates_eq (F := E) (E := TM)
          (F' := ℝ) (E' := fun _ : M ↦ ℝ) (x₀ := x₀) (x := x) (y₀ := x₀) (y := x)
          (ϕ := φ.comp A) hxT (by simp))
  have hφ :
      ∀ z : E,
        ContinuousLinearMap.inCoordinates E TM ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x φ z =
          φ (ex.symm z) := by
    intro z
    simpa [e, ex] using
      congrArg (fun L : E →L[ℝ] ℝ => L z)
        (ContinuousLinearMap.inCoordinates_eq (F := E) (E := TM)
          (F' := ℝ) (E' := fun _ : M ↦ ℝ) (x₀ := x₀) (x := x) (y₀ := x₀) (y := x)
          (ϕ := φ) hxT (by simp))
  have hA :
      ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x A u =
        ex (A (ex.symm u)) := by
    simpa [e, ex] using
      congrArg (fun L : E →L[ℝ] E => L u)
        (ContinuousLinearMap.inCoordinates_eq (F := E) (E := TM)
          (F' := E) (E' := TM) (x₀ := x₀) (x := x) (y₀ := x₀) (y := x)
          (ϕ := A) hxT hxT)
  calc
    ContinuousLinearMap.inCoordinates E TM ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x (φ.comp A) u
      = φ (A (ex.symm u)) := hleft
    _ = φ (ex.symm (ex (A (ex.symm u)))) := by simp
    _ = φ (ex.symm (ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x A u)) := by
          rw [hA]
    _ = ContinuousLinearMap.inCoordinates E TM ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x φ
          (ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x A u) := by
          rw [hφ]
    _ =
        ((ContinuousLinearMap.inCoordinates E TM ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x φ).comp
          (ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x A)) u := by
          simp [ContinuousLinearMap.comp_apply]

end ContinuousLinearMap

namespace ContMDiffAt

theorem compSection
    {φ : ∀ x, TM x →L[ℝ] ℝ} {A : ∀ x, TM x →L[ℝ] TM x} {x₀ : M}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x)) x₀)
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x (A x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x ((φ x).comp (A x))) x₀ := by
  rw [contMDiffAt_hom_bundle (IB := I) (IM := I) (F₁ := E) (E₁ := TM)
    (F₂ := ℝ) (E₂ := fun _ : M ↦ ℝ)
    (f := fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x ((φ x).comp (A x)))]
  refine ⟨contMDiffAt_id, ?_⟩
  change ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) 1
    (fun x ↦ ContinuousLinearMap.inCoordinates E TM ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x
      ((φ x).comp (A x))) x₀
  let Comp :
      (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) →L[ℝ] E →L[ℝ] ℝ :=
    ContinuousLinearMap.compL ℝ E E ℝ
  let Φ : M → E →L[ℝ] ℝ := fun x ↦
    ContinuousLinearMap.inCoordinates E TM ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x (φ x)
  let Ac : M → E →L[ℝ] E := fun x ↦
    ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x (A x)
  have hΦ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) 1 Φ x₀ := by
    simpa [Φ] using
      (((contMDiffAt_hom_bundle
        (IB := I) (IM := I)
        (F₁ := E) (E₁ := TM)
        (F₂ := ℝ) (E₂ := fun _ : M ↦ ℝ)
        (f := fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x))).mp hφ).2)
  have hAc : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) 1 Ac x₀ := by
    simpa [Ac] using
      (((contMDiffAt_hom_bundle
        (IB := I) (IM := I)
        (F₁ := E) (E₁ := TM)
        (F₂ := E) (E₂ := TM)
        (f := fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x (A x))).mp hA).2)
  have hcoord :
      (fun x ↦ (Comp (Φ x)) (Ac x)) =ᶠ[nhds x₀]
        (fun x ↦ ContinuousLinearMap.inCoordinates E TM ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x
          ((φ x).comp (A x))) := by
    have hT : ∀ᶠ x in nhds x₀, x ∈ (trivializationAt E TM x₀).baseSet := by
      exact (trivializationAt E TM x₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E TM x₀)
    filter_upwards [hT] with x hxT
    rw [ContinuousLinearMap.inCoordinates_comp_eq (I := I) (E := E) hxT]
    rfl
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hcoord.symm
  have hComp :
      ContMDiffAt I 𝓘(ℝ, (E →L[ℝ] E) →L[ℝ] E →L[ℝ] ℝ) 1
        (fun x ↦ Comp (Φ x)) x₀ := by
    exact contMDiffAt_const.clm_apply hΦ
  exact hComp.clm_apply hAc

end ContMDiffAt

namespace ContMDiffOn

theorem compSection
    {φ : ∀ x, TM x →L[ℝ] ℝ} {A : ∀ x, TM x →L[ℝ] TM x} {s : Set M}
    (hs : IsOpen s)
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x)) s)
    (hA : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x (A x)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x ((φ x).comp (A x))) s := by
  intro x hx
  exact (ContMDiffAt.compSection
    ((hφ x hx).contMDiffAt (hs.mem_nhds hx))
    ((hA x hx).contMDiffAt (hs.mem_nhds hx))).contMDiffWithinAt

end ContMDiffOn

namespace ContMDiff

theorem compSection
    {φ : ∀ x, TM x →L[ℝ] ℝ} {A : ∀ x, TM x →L[ℝ] TM x}
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x)))
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x (A x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x ((φ x).comp (A x))) := by
  intro x
  exact (hφ x).compSection (I := I) (E := E) (hA x)

end ContMDiff

namespace CovariantDerivative

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- An affine connection is torsion-free if its torsion tensor vanishes. -/
def IsTorsionFree (cov : CovariantDerivative I E TM) : Prop :=
  cov.torsion = 0

/-- Metric compatibility for an affine connection on the tangent bundle with respect to the ambient
Riemannian bundle structure. -/
def IsMetricCompatibleTangent (cov : CovariantDerivative I E TM) : Prop :=
  ∀ {x : M} {σ τ : Π x : M, TangentSpace I x},
    MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      ∀ u : TangentSpace I x,
        mvfderiv (I := I) (fun y ↦ ⟪σ y, τ y⟫) x u =
          ⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫

/-- A Levi-Civita connection is a torsion-free, metric-compatible affine connection. -/
def IsLeviCivita (cov : CovariantDerivative I E TM) : Prop :=
  cov.IsTorsionFree ∧ cov.IsMetricCompatibleTangent

/-- On zero-dimensional tangent fibers, every affine connection is torsion-free. -/
theorem isTorsionFree_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (cov : CovariantDerivative I E TM) :
    cov.IsTorsionFree := by
  ext x u v
  exact Subsingleton.elim _ _

/-- On zero-dimensional tangent fibers, every affine connection is metric-compatible. -/
theorem isMetricCompatibleTangent_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (cov : CovariantDerivative I E TM) :
    cov.IsMetricCompatibleTangent := by
  intro x σ τ _hσ _hτ u
  have hinner : (fun y : M ↦ ⟪σ y, τ y⟫) = 0 := by
    funext y
    have hσy : σ y = 0 := Subsingleton.elim _ _
    have hτy : τ y = 0 := Subsingleton.elim _ _
    simp [hσy, hτy]
  have hcovσ : cov σ x u = 0 := Subsingleton.elim _ _
  have hcovτ : cov τ x u = 0 := Subsingleton.elim _ _
  have hσx : σ x = 0 := Subsingleton.elim _ _
  have hτx : τ x = 0 := Subsingleton.elim _ _
  simp [hinner, hcovσ, hcovτ, hσx, hτx]

/-- On zero-dimensional tangent fibers, every affine connection is Levi-Civita for every
Riemannian metric. -/
theorem isLeviCivita_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (cov : CovariantDerivative I E TM) :
    cov.IsLeviCivita :=
  ⟨cov.isTorsionFree_of_subsingleton_tangent,
    cov.isMetricCompatibleTangent_of_subsingleton_tangent⟩

variable {cov cov' : CovariantDerivative I E TM}

lemma difference_apply_tm (cov cov' : CovariantDerivative I E TM)
    {x : M} {σ : Π x : M, TangentSpace I x}
    (hσ : MDiffAt (T% σ) x) :
    CovariantDerivative.difference cov cov' x (σ x) =
      (cov σ x : TangentSpace I x →L[ℝ] TangentSpace I x) -
        (cov' σ x : TangentSpace I x →L[ℝ] TangentSpace I x) := by
  simpa [CovariantDerivative.difference] using
    (IsCovariantDerivativeOn.difference_apply
      (hcov := CovariantDerivative.isCovariantDerivativeOn cov)
      (hcov' := CovariantDerivative.isCovariantDerivativeOn cov')
      (x := x) (s := Set.univ) (hx := by trivial) (σ := σ) (hσ := hσ))

lemma difference_apply_eq_extend_tm (cov cov' : CovariantDerivative I E TM)
    {x : M} (v : TangentSpace I x) :
    CovariantDerivative.difference cov cov' x v =
      (cov (extend E v) x : TangentSpace I x →L[ℝ] TangentSpace I x) -
        (cov' (extend E v) x : TangentSpace I x →L[ℝ] TangentSpace I x) := by
  simpa using
    (difference_apply_tm cov cov'
      (x := x) (σ := extend E v) (mdifferentiableAt_extend (I := I) (F := E) v))

lemma difference_inner_eq_neg_of_metricCompatible
    (cov cov' : CovariantDerivative I E TM)
    (hcov : cov.IsMetricCompatibleTangent) (hcov' : cov'.IsMetricCompatibleTangent)
    (x : M) (u : TangentSpace I x) (v w : TangentSpace I x) :
    ⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ =
      -⟪v, (CovariantDerivative.difference cov cov' x w) u⟫ := by
  let σ : Π y : M, TangentSpace I y := extend E v
  let τ : Π y : M, TangentSpace I y := extend E w
  have hσ : MDiffAt (T% σ) x := by
    simpa [σ] using (mdifferentiableAt_extend (I := I) (F := E) v)
  have hτ : MDiffAt (T% τ) x := by
    simpa [τ] using (mdifferentiableAt_extend (I := I) (F := E) w)
  have h₁ : mvfderiv (I := I) (fun y ↦ ⟪σ y, τ y⟫) x u =
      ⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫ := hcov hσ hτ u
  have h₂ : mvfderiv (I := I) (fun y ↦ ⟪σ y, τ y⟫) x u =
      ⟪cov' σ x u, τ x⟫ + ⟪σ x, cov' τ x u⟫ := hcov' hσ hτ u
  have hsub :
      (⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫) -
        (⟪cov' σ x u, τ x⟫ + ⟪σ x, cov' τ x u⟫) = 0 := by
    linarith
  have hdiff :
      ⟪cov σ x u - cov' σ x u, τ x⟫ + ⟪σ x, cov τ x u - cov' τ x u⟫ = 0 := by
    calc
      ⟪cov σ x u - cov' σ x u, τ x⟫ + ⟪σ x, cov τ x u - cov' τ x u⟫
          = (⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫) -
              (⟪cov' σ x u, τ x⟫ + ⟪σ x, cov' τ x u⟫) := by
            simp [inner_sub_left, inner_sub_right]
            ring
      _ = 0 := hsub
  have hsum :
      ⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ +
          ⟪v, (CovariantDerivative.difference cov cov' x w) u⟫ = 0 := by
    have hdiffσ := difference_apply_tm cov cov' (x := x) (σ := σ) hσ
    have hdiffτ := difference_apply_tm cov cov' (x := x) (σ := τ) hτ
    have hdiffσ' :
        CovariantDerivative.difference cov cov' x v =
          (cov σ x : TangentSpace I x →L[ℝ] TangentSpace I x) -
            (cov' σ x : TangentSpace I x →L[ℝ] TangentSpace I x) := by
      simpa [σ] using hdiffσ
    have hdiffτ' :
        CovariantDerivative.difference cov cov' x w =
          (cov τ x : TangentSpace I x →L[ℝ] TangentSpace I x) -
            (cov' τ x : TangentSpace I x →L[ℝ] TangentSpace I x) := by
      simpa [τ] using hdiffτ
    rw [hdiffσ', hdiffτ']
    simpa [σ, τ] using hdiff
  linarith

lemma difference_symm_of_isTorsionFree (cov cov' : CovariantDerivative I E TM)
    (hcov : cov.IsTorsionFree) (hcov' : cov'.IsTorsionFree)
    (x : M) (u v : TangentSpace I x) :
    (CovariantDerivative.difference cov cov' x v) u =
      (CovariantDerivative.difference cov cov' x u) v := by
  have hcov_zero : CovariantDerivative.torsion cov x u v = 0 := by
    simpa [CovariantDerivative.IsTorsionFree] using congr(($hcov x u v))
  have hcov'_zero : CovariantDerivative.torsion cov' x u v = 0 := by
    simpa [CovariantDerivative.IsTorsionFree] using congr(($hcov' x u v))
  have hcov_eq :
      cov (extend E v) x u - cov (extend E u) x v =
        VectorField.mlieBracket I (extend E u) (extend E v) x := by
    have haux :
        cov (extend E v) x u - cov (extend E u) x v -
          VectorField.mlieBracket I (extend E u) (extend E v) x = 0 := by
      simpa [hcov_zero] using (CovariantDerivative.torsion_apply_eq_extend cov (x := x) u v).symm
    exact sub_eq_zero.mp haux
  have hcov'_eq :
      cov' (extend E v) x u - cov' (extend E u) x v =
        VectorField.mlieBracket I (extend E u) (extend E v) x := by
    have haux :
        cov' (extend E v) x u - cov' (extend E u) x v -
          VectorField.mlieBracket I (extend E u) (extend E v) x = 0 := by
      simpa [hcov'_zero] using
        (CovariantDerivative.torsion_apply_eq_extend cov' (x := x) u v).symm
    exact sub_eq_zero.mp haux
  have hEq :
      cov (extend E v) x u - cov (extend E u) x v =
        cov' (extend E v) x u - cov' (extend E u) x v := by
    rw [hcov_eq, hcov'_eq]
  have hdiff :
      cov (extend E v) x u - cov' (extend E v) x u =
        cov (extend E u) x v - cov' (extend E u) x v := by
    have htmp :=
      congrArg
        (fun z ↦ z + (cov (extend E u) x v - cov' (extend E v) x u))
        hEq
    abel_nf at htmp ⊢
    exact htmp
  simpa [difference_apply_eq_extend_tm cov cov' v, difference_apply_eq_extend_tm cov cov' u]
    using hdiff

theorem difference_eq_zero_of_isLeviCivita (cov cov' : CovariantDerivative I E TM)
    (hcov : cov.IsLeviCivita) (hcov' : cov'.IsLeviCivita) :
    CovariantDerivative.difference cov cov' = 0 := by
  ext x v u
  apply ext_inner_right ℝ
  intro w
  have h₁ := difference_inner_eq_neg_of_metricCompatible cov cov' hcov.2 hcov'.2
    x u v w
  have h₂ := difference_inner_eq_neg_of_metricCompatible cov cov' hcov.2 hcov'.2
    x w u v
  have h₃ := difference_inner_eq_neg_of_metricCompatible cov cov' hcov.2 hcov'.2
    x v w u
  have hs₁ := difference_symm_of_isTorsionFree cov cov' hcov.1 hcov'.1 x w u
  have hs₂ := difference_symm_of_isTorsionFree cov cov' hcov.1 hcov'.1 x v w
  have hs₃ := difference_symm_of_isTorsionFree cov cov' hcov.1 hcov'.1 x u v
  have hneg :
      ⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ =
        -⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ := by
    calc
      ⟪(CovariantDerivative.difference cov cov' x v) u, w⟫
          = -⟪v, (CovariantDerivative.difference cov cov' x w) u⟫ := h₁
      _ = -⟪(CovariantDerivative.difference cov cov' x w) u, v⟫ := by rw [real_inner_comm]
      _ = -⟪(CovariantDerivative.difference cov cov' x u) w, v⟫ := by rw [hs₁]
      _ = ⟪u, (CovariantDerivative.difference cov cov' x v) w⟫ := by
        linarith
      _ = ⟪(CovariantDerivative.difference cov cov' x v) w, u⟫ := by rw [real_inner_comm]
      _ = ⟪(CovariantDerivative.difference cov cov' x w) v, u⟫ := by rw [hs₂]
      _ = -⟪w, (CovariantDerivative.difference cov cov' x u) v⟫ := by
        linarith
      _ = -⟪(CovariantDerivative.difference cov cov' x u) v, w⟫ := by rw [real_inner_comm]
      _ = -⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ := by rw [hs₃]
  have hzero : ⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ = 0 := by
    linarith
  simpa using hzero

lemma eq_of_isLeviCivita (cov cov' : CovariantDerivative I E TM)
    (hcov : cov.IsLeviCivita) (hcov' : cov'.IsLeviCivita)
    {x : M} {σ : Π x : M, TangentSpace I x} (hσ : MDiffAt (T% σ) x) :
    cov σ x = cov' σ x := by
  have hdiff : CovariantDerivative.difference cov cov' = 0 :=
    difference_eq_zero_of_isLeviCivita cov cov' hcov hcov'
  have hzero : CovariantDerivative.difference cov cov' x (σ x) = 0 := by
    simpa using congr(($hdiff x (σ x)))
  have hmaps : cov σ x - cov' σ x = 0 := by
    simpa [difference_apply_tm cov cov' hσ] using hzero
  exact sub_eq_zero.mp hmaps

lemma isMetricCompatibleTangent_iff_of_inner_eq
    (cov : CovariantDerivative I E TM)
    {n : WithTop ℕ∞}
    {g g' : Bundle.ContMDiffRiemannianMetric I n E TM}
    (hinner : ∀ x : M, ∀ u v : TM x, g.inner x u v = g'.inner x u v) :
    (letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩; cov.IsMetricCompatibleTangent) ↔
      (letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩;
        cov.IsMetricCompatibleTangent) := by
  have hmetric : g = g' := by
    exact Bundle.ContMDiffRiemannianMetric.ext hinner
  subst hmetric
  rfl

lemma isLeviCivita_iff_of_inner_eq
    (cov : CovariantDerivative I E TM)
    {n : WithTop ℕ∞}
    {g g' : Bundle.ContMDiffRiemannianMetric I n E TM}
    (hinner : ∀ x : M, ∀ u v : TM x, g.inner x u v = g'.inner x u v) :
    (letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩; cov.IsLeviCivita) ↔
      (letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩; cov.IsLeviCivita) := by
  have hmetric : g = g' := by
    exact Bundle.ContMDiffRiemannianMetric.ext hinner
  subst hmetric
  rfl

theorem affineConnection_nonempty [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    Nonempty (CovariantDerivative I E TM) :=
  CovariantDerivative.nonempty (I := I) (F := E) (V := TM)

/-- The tangent bundle admits a global `C^1` affine connection. -/
theorem affineConnection_contMDiff_nonempty [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    Nonempty { cov : CovariantDerivative I E TM // ContMDiffCovariantDerivative cov 1 } :=
  CovariantDerivative.contMDiff_nonempty (I := I) (F := E) (V := TM)

theorem exists_contMDiffAffineConnection [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    ∃ cov : CovariantDerivative I E TM, ContMDiffCovariantDerivative cov 1 := by
  rcases affineConnection_contMDiff_nonempty (I := I) (E := E) (M := M) with ⟨⟨cov, hcov⟩⟩
  exact ⟨cov, hcov⟩

/-- The tangent bundle admits a global `C^2` affine connection. -/
theorem affineConnection_contMDiff_nonempty_two
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    Nonempty { cov : CovariantDerivative I E TM // ContMDiffCovariantDerivative cov 2 } :=
  CovariantDerivative.contMDiff_nonempty_two (I := I) (F := E) (V := TM)

theorem exists_contMDiffAffineConnection_two
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    ∃ cov : CovariantDerivative I E TM, ContMDiffCovariantDerivative cov 2 := by
  rcases affineConnection_contMDiff_nonempty_two (I := I) (E := E) (M := M) with ⟨⟨cov, hcov⟩⟩
  exact ⟨cov, hcov⟩

section Existence

variable (cov : CovariantDerivative I E TM)

noncomputable def metricDefectAux (cov : CovariantDerivative I E TM) (x : M)
    (σ τ : Π y : M, TangentSpace I y) :
    TangentSpace I x →L[ℝ] ℝ :=
  mvfderiv (I := I) (fun y ↦ ⟪σ y, τ y⟫) x -
    (InnerProductSpace.toDual ℝ (TangentSpace I x) (τ x)).comp (cov σ x) -
    (InnerProductSpace.toDual ℝ (TangentSpace I x) (σ x)).comp (cov τ x)

lemma metricDefectAux_apply (cov : CovariantDerivative I E TM) (x : M)
    (σ τ : Π y : M, TangentSpace I y) (u : TangentSpace I x) :
    metricDefectAux cov x σ τ u =
      mvfderiv (I := I) (fun y ↦ ⟪σ y, τ y⟫) x u -
        ⟪cov σ x u, τ x⟫ - ⟪σ x, cov τ x u⟫ := by
  simp [metricDefectAux, real_inner_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma metricDefectAux_symm (cov : CovariantDerivative I E TM) (x : M)
    (σ τ : Π y : M, TangentSpace I y) :
    metricDefectAux cov x σ τ = metricDefectAux cov x τ σ := by
  ext u
  rw [metricDefectAux_apply, metricDefectAux_apply]
  simp [real_inner_comm, add_assoc, add_left_comm, add_comm]
  ring_nf

lemma mdiffAt_inner_sections {x : M}
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    MDiffAt (fun y ↦ ⟪σ y, τ y⟫) x := by
  rcases (show IsContMDiffRiemannianBundle I 1 E TM from inferInstance).exists_contMDiff with
    ⟨g, hg, hinner⟩
  have hgAt : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun y : M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (g y)) x := by
    exact hg.mdifferentiableAt one_ne_zero
  have happly : MDifferentiableAt I (I.prod 𝓘(ℝ))
      (fun y : M ↦ TotalSpace.mk' ℝ y (g y (σ y) (τ y))) x := by
    apply MDifferentiableAt.clm_bundle_apply₂ (IB := I) (IM := I)
      (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TM) (E₂ := TM) (E₃ := fun _ : M ↦ ℝ) (b := fun y : M ↦ y)
    · exact hgAt
    · exact hσ
    · exact hτ
  let e : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    trivializationAt ℝ (fun _ : M ↦ ℝ) x
  have hex : (TotalSpace.mk' ℝ x (g x (σ x) (τ x)) : TotalSpace ℝ (fun _ : M ↦ ℝ)) ∈ e.source := by
    simpa [e] using
      FiberBundle.mem_trivializationAt_source ℝ (fun _ : M ↦ ℝ)
        (TotalSpace.mk' ℝ x (g x (σ x) (τ x)))
  have hiff :=
    (Bundle.Trivialization.mdifferentiableAt_totalSpace_iff (IB := I) (IM := I) (e := e)
      (f := fun y : M ↦ TotalSpace.mk' ℝ y (g y (σ y) (τ y))) (x₀ := x) hex).mp happly
  simpa [e, hinner] using hiff.2

theorem contMDiffOn_metricDefectAux_section
    [IsContMDiffRiemannianBundle I 2 E TM]
    {s : Set M} (hs : IsOpen s)
    {cov : CovariantDerivative I E TM}
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun s)
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)) s)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (metricDefectAux cov x σ τ)) s := by
  have hinner : ContMDiffOn I 𝓘(ℝ) 2 (fun y ↦ ⟪σ y, τ y⟫) s := by
    exact ContMDiffOn.inner_bundle (IM := I) (IB := I) (F := E) (E := TM)
      (b := id) (v := σ) (w := τ) hσ hτ
  have hext :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (mvfderiv (I := I) (fun y ↦ ⟪σ y, τ y⟫) x)) s := by
    intro x hx
    exact (((hinner x hx).contMDiffAt (hs.mem_nhds hx)).extDerivSection
      (I := I) (E := E) (m := 1) (n := 2) (by norm_num)).contMDiffWithinAt
  have hcovσ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x (cov σ x)) s :=
    hcov.contMDiff hσ
  have hcovτ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x (cov τ x)) s :=
    hcov.contMDiff hτ
  have hτdual :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (InnerProductSpace.toDual ℝ (TM x) (τ x))) s := by
    exact (hτ.of_le (by norm_num)).toDualSection (I := I) (E := E)
  have hσdual :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (InnerProductSpace.toDual ℝ (TM x) (σ x))) s := by
    exact (hσ.of_le (by norm_num)).toDualSection (I := I) (E := E)
  have htermστ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          ((InnerProductSpace.toDual ℝ (TM x) (τ x)).comp (cov σ x))) s := by
    exact hτdual.compSection (I := I) (E := E) hs hcovσ
  have htermτσ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          ((InnerProductSpace.toDual ℝ (TM x) (σ x)).comp (cov τ x))) s := by
    exact hσdual.compSection (I := I) (E := E) hs hcovτ
  simpa [metricDefectAux] using (hext.sub_section htermστ).sub_section htermτσ

theorem contMDiff_metricDefectAux_section
    [IsContMDiffRiemannianBundle I 2 E TM]
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 1]
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (metricDefectAux cov x σ τ)) := by
  simpa [contMDiffOn_univ] using
    (contMDiffOn_metricDefectAux_section (I := I) (E := E) (s := Set.univ) isOpen_univ
      (inferInstance : ContMDiffCovariantDerivative cov 1).contMDiff
      (by simpa [contMDiffOn_univ] using hσ)
      (by simpa [contMDiffOn_univ] using hτ))

theorem contMDiffOn_torsion_section
    [IsManifold I 3 M]
    {s : Set M} (hs : IsOpen s)
    {cov : CovariantDerivative I E TM}
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun s)
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)) s)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (cov.torsion x (σ x) (τ x))) s := by
  have hσ₁ := hσ.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)
  have hτ₁ := hτ.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)
  have hcovσ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x (cov σ x)) s :=
    hcov.contMDiff hσ
  have hcovτ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x (cov τ x)) s :=
    hcov.contMDiff hτ
  have hAlongστ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along σ τ y)) s := by
    simpa [CovariantDerivative.along] using hcovτ.clm_bundle_apply hσ₁
  have hAlongτσ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along τ σ y)) s := by
    simpa [CovariantDerivative.along] using hcovσ.clm_bundle_apply hτ₁
  letI : IsManifold I (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold I 2 M)
  letI : IsManifold I ((2 : ℕ∞) + 1) M := by
    apply IsManifold.of_le (n := 3)
    norm_num
  have hBracketWithin :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (VectorField.mlieBracketWithin I σ τ s y)) s := by
    simpa using
      (hσ.mlieBracketWithin_vectorField (I := I) (m := (1 : ℕ∞)) hτ hs.uniqueMDiffOn
        (by norm_num))
  have hBracket :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (VectorField.mlieBracket I σ τ y)) s := by
    refine ContMDiffOn.congr hBracketWithin ?_
    intro x hx
    have hσx : MDiffAt (T% σ) x := by
      exact ((((hσ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
          (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero)
    have hτx : MDiffAt (T% τ) x := by
      exact ((((hτ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
          (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero)
    congr 1
    simpa using
      (VectorField.mlieBracketWithin_eq_mlieBracket (I := I) (s := s) (x := x)
        (hs.uniqueMDiffWithinAt hx) hσx hτx).symm
  have hEq :
      Set.EqOn
        (fun x ↦ TotalSpace.mk' E x (cov.torsion x (σ x) (τ x)))
        (fun x ↦ TotalSpace.mk' E x
          (cov.along σ τ x - cov.along τ σ x - VectorField.mlieBracket I σ τ x))
        s := by
    intro x hx
    congr 1
    simpa [CovariantDerivative.along] using
      (cov.torsion_apply
        ((((hσ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
            (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero)
        ((((hτ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
            (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero))
  refine ContMDiffOn.congr ((hAlongστ.sub_section hAlongτσ).sub_section hBracket) ?_
  intro x hx
  simpa using (hEq hx)

theorem contMDiff_torsion_section
    [IsManifold I 3 M]
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 1]
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (cov.torsion x (σ x) (τ x))) := by
  simpa [contMDiffOn_univ] using
    (contMDiffOn_torsion_section (I := I) (E := E) (s := Set.univ) isOpen_univ
      (inferInstance : ContMDiffCovariantDerivative cov 1).contMDiff
      (by simpa [contMDiffOn_univ] using hσ)
      (by simpa [contMDiffOn_univ] using hτ))

theorem metricDefectAux_tensorial_left (cov : CovariantDerivative I E TM) (x : M)
    (τ : Π y : M, TangentSpace I y) (hτ : MDiffAt (T% τ) x) :
    TensorialAt I E (fun σ ↦ metricDefectAux cov x σ τ) x := by
  refine ⟨?_, ?_⟩
  · intro f σ hf hσ
    ext u
    have hinner : MDiffAt (fun y ↦ ⟪σ y, τ y⟫) x := mdiffAt_inner_sections (hσ := hσ) (hτ := hτ)
    have hprod :
        mvfderiv (I := I) (fun y ↦ f y * ⟪σ y, τ y⟫) x u =
          f x * mvfderiv (I := I) (fun y ↦ ⟪σ y, τ y⟫) x u +
            ⟪σ x, τ x⟫ * mvfderiv (I := I) f x u := by
      have hfun : (fun y ↦ f y * ⟪σ y, τ y⟫) =
          f * (fun y ↦ ⟪σ y, τ y⟫) := by
        rfl
      have hmul := congrArg (fun L => L u)
        (mvfderiv_mul (I := I) hf hinner)
      rw [← hfun] at hmul
      simpa [smul_eq_mul] using hmul
    have hcov :=
      (CovariantDerivative.isCovariantDerivativeOn cov).leibniz hσ hf (x := x)
    have hcovu :
        cov (f • σ) x u = f x • cov σ x u + mvfderiv (I := I) f x u • σ x := by
      simpa using congr(($hcov u))
    rw [metricDefectAux_apply]
    conv_rhs =>
      rw [show (f x • cov.metricDefectAux x σ τ) u = f x * (cov.metricDefectAux x σ τ) u by rfl]
      rw [show (cov.metricDefectAux x σ τ) u = metricDefectAux cov x σ τ u by rfl]
      rw [metricDefectAux_apply]
    simp [hprod, hcovu, Pi.smul_apply, inner_add_left, real_inner_smul_left]
    ring_nf
  · intro σ σ' hσ hσ'
    ext u
    have hinnerσ : MDiffAt (fun y ↦ ⟪σ y, τ y⟫) x := mdiffAt_inner_sections (hσ := hσ) (hτ := hτ)
    have hinnerσ' : MDiffAt (fun y ↦ ⟪σ' y, τ y⟫) x :=
      mdiffAt_inner_sections (hσ := hσ') (hτ := hτ)
    have hinner :
        mvfderiv (I := I) (fun y ↦ ⟪(σ + σ') y, τ y⟫) x =
          mvfderiv (I := I) (fun y ↦ ⟪σ y, τ y⟫) x +
            mvfderiv (I := I) (fun y ↦ ⟪σ' y, τ y⟫) x := by
      have hsum :
          (fun y ↦ ⟪(σ + σ') y, τ y⟫) =
            (fun y ↦ ⟪σ y, τ y⟫) + fun y ↦ ⟪σ' y, τ y⟫ := by
        funext y
        simp [inner_add_left]
      rw [hsum, mvfderiv_add hinnerσ hinnerσ']
    have hcov :=
      (CovariantDerivative.isCovariantDerivativeOn cov).add hσ hσ' (x := x)
    rw [metricDefectAux_apply]
    rw [show (cov.metricDefectAux x σ τ + cov.metricDefectAux x σ' τ) u =
        (cov.metricDefectAux x σ τ) u + (cov.metricDefectAux x σ' τ) u by rfl]
    rw [show (cov.metricDefectAux x σ τ) u = metricDefectAux cov x σ τ u by rfl]
    rw [show (cov.metricDefectAux x σ' τ) u = metricDefectAux cov x σ' τ u by rfl]
    rw [metricDefectAux_apply, metricDefectAux_apply, hinner]
    simp [hcov, inner_add_left, inner_add_right, add_assoc, add_left_comm, add_comm]
    ring_nf

theorem metricDefectAux_tensorial_right (cov : CovariantDerivative I E TM) (x : M)
    (σ : Π y : M, TangentSpace I y) (hσ : MDiffAt (T% σ) x) :
    TensorialAt I E (fun τ ↦ metricDefectAux cov x σ τ) x := by
  let hleft := metricDefectAux_tensorial_left cov x σ hσ
  refine ⟨?_, ?_⟩
  · intro f τ hf hτ
    calc
      metricDefectAux cov x σ (f • τ)
          = metricDefectAux cov x (f • τ) σ := by
              simpa using metricDefectAux_symm cov x σ (f • τ)
      _ = f x • metricDefectAux cov x τ σ := hleft.smul hf hτ
      _ = f x • metricDefectAux cov x σ τ := by
            rw [metricDefectAux_symm cov x τ σ]
  · intro τ τ' hτ hτ'
    calc
      metricDefectAux cov x σ (τ + τ')
          = metricDefectAux cov x (τ + τ') σ := by
              simpa using metricDefectAux_symm cov x σ (τ + τ')
      _ = metricDefectAux cov x τ σ + metricDefectAux cov x τ' σ :=
            hleft.add hτ hτ'
      _ = metricDefectAux cov x σ τ + metricDefectAux cov x σ τ' := by
            rw [metricDefectAux_symm cov x τ σ,
              metricDefectAux_symm cov x τ' σ]

/-- The pointwise metric defect of an affine connection, viewed as a trilinear map. Its arguments are
ordered as `(v, w, u)`, so `cov.metricDefect x v w u` equals the usual defect
`Dₓ(u, v, w)`. -/
noncomputable def metricDefect (cov : CovariantDerivative I E TM) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂
    (I := I) (F := E) (F' := E)
    (fun σ τ ↦ metricDefectAux cov x σ τ) x
    (fun τ hτ ↦ metricDefectAux_tensorial_left cov x τ hτ)
    (fun σ hσ ↦ metricDefectAux_tensorial_right cov x σ hσ)

lemma metricDefect_apply (cov : CovariantDerivative I E TM) (x : M) (u v w : TangentSpace I x) :
    cov.metricDefect x v w u =
      mvfderiv (I := I) (fun y ↦ ⟪extend E v y, extend E w y⟫) x u -
        ⟪cov (extend E v) x u, w⟫ - ⟪v, cov (extend E w) x u⟫ := by
  have h := congrArg (fun f ↦ f u)
    (TensorialAt.mkHom₂_apply_eq_extend
      (I := I) (F := E) (F' := E)
      (Φ := fun σ τ ↦ metricDefectAux cov x σ τ) (x := x)
      (hΦ₁ := fun τ hτ ↦ metricDefectAux_tensorial_left cov x τ hτ)
      (hΦ₂ := fun σ hσ ↦ metricDefectAux_tensorial_right cov x σ hσ)
      v w)
  simpa [metricDefect, metricDefectAux_apply] using h

lemma metricDefect_apply_sections (cov : CovariantDerivative I E TM) {x : M}
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    cov.metricDefect x (σ x) (τ x) = metricDefectAux cov x σ τ := by
  simpa [metricDefect] using
    (TensorialAt.mkHom₂_apply
      (I := I) (F := E) (F' := E)
      (Φ := fun σ τ ↦ metricDefectAux cov x σ τ) (x := x)
      (hΦ₁ := fun τ hτ ↦ metricDefectAux_tensorial_left cov x τ hτ)
      (hΦ₂ := fun σ hσ ↦ metricDefectAux_tensorial_right cov x σ hσ)
      hσ hτ)

theorem contMDiffOn_metricDefect_section
    [IsContMDiffRiemannianBundle I 2 E TM]
    {s : Set M} (hs : IsOpen s)
    {cov : CovariantDerivative I E TM}
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun s)
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)) s)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (cov.metricDefect x (σ x) (τ x))) s := by
  refine ContMDiffOn.congr
    (contMDiffOn_metricDefectAux_section (I := I) (E := E) hs hcov hσ hτ) ?_
  intro x hx
  refine congrArg (fun φ ↦ TotalSpace.mk' (E := TStar) (E →L[ℝ] ℝ) x φ) ?_
  exact cov.metricDefect_apply_sections
    ((((hσ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
        (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero)
    ((((hτ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
        (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero)

theorem contMDiff_metricDefect_section
    [IsContMDiffRiemannianBundle I 2 E TM]
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 1]
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (cov.metricDefect x (σ x) (τ x))) := by
  simpa [contMDiffOn_univ] using
    (contMDiffOn_metricDefect_section (I := I) (E := E) (s := Set.univ) isOpen_univ
      (inferInstance : ContMDiffCovariantDerivative cov 1).contMDiff
      (by simpa [contMDiffOn_univ] using hσ)
      (by simpa [contMDiffOn_univ] using hτ))

lemma metricDefect_symm (cov : CovariantDerivative I E TM) (x : M) (v w : TangentSpace I x) :
    cov.metricDefect x v w = cov.metricDefect x w v := by
  ext u
  simp only [metricDefect_apply]
  have hext : mvfderiv (I := I) (fun y ↦ ⟪extend E v y, extend E w y⟫) x u =
      mvfderiv (I := I) (fun y ↦ ⟪extend E w y, extend E v y⟫) x u := by
    have hswap :
        (fun y ↦ ⟪extend E v y, extend E w y⟫) =
          fun y ↦ ⟪extend E w y, extend E v y⟫ := by
      funext y
      exact real_inner_comm _ _
    rw [hswap]
  linarith [hext, real_inner_comm (cov (extend E v) x u) w,
            real_inner_comm v (cov (extend E w) x u)]

lemma isMetricCompatibleTangent_iff_metricDefect_eq_zero
    (cov : CovariantDerivative I E TM) :
    cov.IsMetricCompatibleTangent ↔
      ∀ (x : M) (v w : TangentSpace I x), cov.metricDefect x v w = 0 := by
  constructor
  · intro h x v w
    ext u
    simp only [ContinuousLinearMap.zero_apply, metricDefect_apply]
    have hcompat :=
      h (x := x) (σ := extend E v) (τ := extend E w)
        (by simpa using (mdifferentiableAt_extend (I := I) (F := E) v))
        (by simpa using (mdifferentiableAt_extend (I := I) (F := E) w))
        u
    have hcompat' : mvfderiv (I := I) (fun y ↦ ⟪extend E v y, extend E w y⟫) x u =
        ⟪cov (extend E v) x u, w⟫ + ⟪v, cov (extend E w) x u⟫ := by simpa using hcompat
    linarith
  · intro h
    intro x σ τ hσ hτ u
    have haux : metricDefectAux cov x σ τ = 0 := by
      rw [← cov.metricDefect_apply_sections (x := x) hσ hτ]
      exact h x (σ x) (τ x)
    have hauxu : metricDefectAux cov x σ τ u = 0 := by
      simpa using congr(($haux u))
    rw [metricDefectAux_apply] at hauxu
    linarith

noncomputable def flipLastTwo (x : M) :
    ((TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearEquiv.toContinuousLinearMap
    ((ContinuousLinearMap.flipₗᵢ ℝ (TangentSpace I x) (TangentSpace I x) ℝ).toContinuousLinearEquiv)

@[simp] lemma flipLastTwo_apply (x : M)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (u v : TangentSpace I x) :
    flipLastTwo (I := I) x B u v = B v u := rfl

noncomputable def torsionInnerFunctional (cov : CovariantDerivative I E TM) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ))
      ((InnerProductSpace.toDualMap ℝ (TangentSpace I x)).toContinuousLinearMap)).comp
    (cov.torsion x)

@[simp] lemma torsionInnerFunctional_apply (cov : CovariantDerivative I E TM) (x : M)
    (u v w : TangentSpace I x) :
    torsionInnerFunctional (I := I) cov x u v w = ⟪cov.torsion x u v, w⟫ := by
  rw [torsionInnerFunctional, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    InnerProductSpace.toContinuousLinearMap_toDualMap]
  rfl

theorem contMDiffOn_torsionInner_section
    [IsManifold I 3 M]
    {s : Set M} (hs : IsOpen s)
    {cov : CovariantDerivative I E TM}
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun s)
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)) s)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (torsionInnerFunctional (I := I) cov x (σ x) (τ x))) s := by
  have hdual :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (InnerProductSpace.toDual ℝ (TM x) (cov.torsion x (σ x) (τ x)))) s := by
    exact
      (contMDiffOn_torsion_section (I := I) (E := E) hs hcov hσ hτ).toDualSection (I := I)
        (E := E)
  refine ContMDiffOn.congr hdual ?_
  intro x hx
  refine congrArg (fun φ ↦ TotalSpace.mk' (E := TStar) (E →L[ℝ] ℝ) x φ) ?_
  ext w
  simp [torsionInnerFunctional_apply]

theorem contMDiff_torsionInner_section
    [IsManifold I 3 M]
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 1]
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (torsionInnerFunctional (I := I) cov x (σ x) (τ x))) := by
  simpa [contMDiffOn_univ] using
    (contMDiffOn_torsionInner_section (I := I) (E := E) (s := Set.univ) isOpen_univ
      (inferInstance : ContMDiffCovariantDerivative cov 1).contMDiff
      (by simpa [contMDiffOn_univ] using hσ)
      (by simpa [contMDiffOn_univ] using hτ))

noncomputable def swapFirstTwoMap (x : M)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) := by
  letI : AddCommGroup (TangentSpace I x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
  letI : Module ℝ (TangentSpace I x →L[ℝ] ℝ) := ContinuousLinearMap.module
  letI : AddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup
  letI : Module ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.module
  exact
    LinearMap.toContinuousLinearMap
      { toFun := fun v =>
          LinearMap.toContinuousLinearMap
            { toFun := fun u =>
                LinearMap.toContinuousLinearMap
                  { toFun := fun w => B u v w
                    map_add' := by
                      intro w₁ w₂
                      simpa [ContinuousLinearMap.add_apply] using
                        congrArg (fun F => F w₁ + F w₂) (B u v).map_add w₁ w₂
                    map_smul' := by
                      intro c w
                      simpa [ContinuousLinearMap.smul_apply, RingHom.id_apply] using
                        congrArg (fun F => F w) ((B u v).map_smulₛₗ c w) }
              map_add' := by
                intro u₁ u₂
                ext w
                simpa [ContinuousLinearMap.add_apply] using
                  congrArg (fun F => F v w) (B.map_add u₁ u₂)
              map_smul' := by
                intro c u
                ext w
                simpa [ContinuousLinearMap.smul_apply, RingHom.id_apply] using
                  congrArg (fun F => F v w) (B.map_smulₛₗ c u) }
        map_add' := by
          intro v₁ v₂
          ext u w
          simpa [ContinuousLinearMap.add_apply] using
            congrArg (fun F => F u w) ((B u).map_add v₁ v₂)
        map_smul' := by
          intro c v
          ext u w
          simpa [ContinuousLinearMap.smul_apply, RingHom.id_apply] using
            congrArg (fun F => F u w) ((B u).map_smulₛₗ c v) }

@[simp] lemma swapFirstTwoMap_apply (x : M)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ))
    (v u w : TangentSpace I x) :
    swapFirstTwoMap (I := I) x B v u w = B u v w := rfl

noncomputable def reverseArgs (x : M)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  by
    letI : AddCommGroup (TangentSpace I x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
    letI : Module ℝ (TangentSpace I x →L[ℝ] ℝ) := ContinuousLinearMap.module
    letI : AddCommGroup
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
      ContinuousLinearMap.addCommGroup
    letI : Module ℝ
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
      ContinuousLinearMap.module
    exact
      LinearMap.toContinuousLinearMap
        { toFun := fun v =>
            LinearMap.toContinuousLinearMap
              { toFun := fun u =>
                  LinearMap.toContinuousLinearMap
                    { toFun := fun w => B w u v
                      map_add' := by
                        intro w₁ w₂
                        simpa [ContinuousLinearMap.add_apply] using
                          congrArg (fun F => F u v) (B.map_add w₁ w₂)
                      map_smul' := by
                        intro c w
                        simpa [ContinuousLinearMap.smul_apply, RingHom.id_apply] using
                          congrArg (fun F => F u v) (B.map_smulₛₗ c w) }
                map_add' := by
                  intro u₁ u₂
                  ext w
                  simpa [ContinuousLinearMap.add_apply] using
                    congrArg (fun F => F v) ((B w).map_add u₁ u₂)
                map_smul' := by
                  intro c u
                  ext w
                  simpa [ContinuousLinearMap.smul_apply, RingHom.id_apply] using
                    congrArg (fun F => F v) ((B w).map_smulₛₗ c u) }
          map_add' := by
            intro v₁ v₂
            ext u w
            simpa using (B w u).map_add v₁ v₂
          map_smul' := by
            intro c v
            ext u w
            simpa [RingHom.id_apply] using (B w u).map_smulₛₗ c v }

@[simp] lemma reverseArgs_apply (x : M)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ))
    (v u w : TangentSpace I x) :
    reverseArgs (I := I) x B v u w = B w u v := rfl
noncomputable def correctionFunctional (cov : CovariantDerivative I E TM) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  let Tri :
      Type _ := TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)
  let _ : AddCommGroup (TangentSpace I x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
  let _ : Module ℝ (TangentSpace I x →L[ℝ] ℝ) := ContinuousLinearMap.module
  let _ : AddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup
  let _ : Module ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.module
  let _ : AddCommGroup Tri := ContinuousLinearMap.addCommGroup
  let _ : Module ℝ Tri := ContinuousLinearMap.module
  let D : Tri := cov.metricDefect x
  let T : Tri := torsionInnerFunctional (I := I) cov x
  let swap23 :
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
      flipLastTwo (I := I) x
  let term1 : Tri := swap23.comp D
  let term2 : Tri := swapFirstTwoMap (I := I) x term1
  let term3 : Tri := swapFirstTwoMap (I := I) x D
  let term4 : Tri := swapFirstTwoMap (I := I) x T
  let term5 : Tri := swap23.comp T
  let term6 : Tri := reverseArgs (I := I) x T
  let C : Tri :=
    term1 + term2 - term3 - term4 + term5 - term6
  (1 / 2 : ℝ) • C

@[simp] lemma correctionFunctional_apply (cov : CovariantDerivative I E TM) (x : M)
    (v u w : TangentSpace I x) :
    correctionFunctional cov x v u w =
      (cov.metricDefect x v w u + cov.metricDefect x u w v - cov.metricDefect x u v w -
          ⟪cov.torsion x u v, w⟫ + ⟪cov.torsion x v w, u⟫ - ⟪cov.torsion x w u, v⟫) / 2 := by
  letI : AddCommGroup (TangentSpace I x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
  letI : Module ℝ (TangentSpace I x →L[ℝ] ℝ) := ContinuousLinearMap.module
  letI : AddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup
  letI : Module ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.module
  simp [correctionFunctional, swapFirstTwoMap, reverseArgs, flipLastTwo,
    torsionInnerFunctional, ContinuousLinearMap.comp_apply, sub_eq_add_neg, smul_eq_mul]
  ring_nf
  rfl

noncomputable def continuousDualBasis {ι : Type*} (b : Module.Basis ι ℝ E) :
    Module.Basis ι ℝ (E →L[ℝ] ℝ) := by
  classical
  letI := FiniteDimensional.fintypeBasisIndex b
  exact b.dualBasis.map
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ))

@[simp] theorem continuousDualBasis_repr {ι : Type*} (b : Module.Basis ι ℝ E)
    (φ : E →L[ℝ] ℝ) (i : ι) :
    (continuousDualBasis b).repr φ i = φ (b i) := by
  classical
  letI := FiniteDimensional.fintypeBasisIndex b
  change (((LinearMap.toContinuousLinearMap :
      (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).symm.trans b.dualBasis.repr) φ) i = φ (b i)
  simp [Module.Basis.dualBasis_repr]

theorem contMDiffOn_correctionFunctional_apply_section
    [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E TM]
    {u : Set M} (hu : IsOpen u)
    {cov : CovariantDerivative I E TM}
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun u)
    {σ τ υ : Π y : M, TangentSpace I y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)) u)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y)) u)
    (hυ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (υ y)) u) :
    ContMDiffOn I 𝓘(ℝ) 1
      (fun x ↦ correctionFunctional cov x (σ x) (τ x) (υ x)) u := by
  have hσ₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (σ y)) u :=
    hσ.of_le (by norm_num)
  have hτ₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (τ y)) u :=
    hτ.of_le (by norm_num)
  have hυ₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (υ y)) u :=
    hυ.of_le (by norm_num)
  have hmetricσυ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (cov.metricDefect x (σ x) (υ x))) u :=
    contMDiffOn_metricDefect_section (I := I) (E := E) hu hcov hσ hυ
  have hmetricτυ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (cov.metricDefect x (τ x) (υ x))) u :=
    contMDiffOn_metricDefect_section (I := I) (E := E) hu hcov hτ hυ
  have hmetricτσ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (cov.metricDefect x (τ x) (σ x))) u :=
    contMDiffOn_metricDefect_section (I := I) (E := E) hu hcov hτ hσ
  have hterm1 :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 1
        (fun x ↦ TotalSpace.mk' ℝ x (cov.metricDefect x (σ x) (υ x) (τ x))) u := by
    simpa using hmetricσυ.clm_bundle_apply hτ₁
  have hterm2 :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 1
        (fun x ↦ TotalSpace.mk' ℝ x (cov.metricDefect x (τ x) (υ x) (σ x))) u := by
    simpa using hmetricτυ.clm_bundle_apply hσ₁
  have hterm3 :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 1
        (fun x ↦ TotalSpace.mk' ℝ x (cov.metricDefect x (τ x) (σ x) (υ x))) u := by
    simpa using hmetricτσ.clm_bundle_apply hυ₁
  have htorsτσ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (torsionInnerFunctional (I := I) cov x (τ x) (σ x))) u :=
    contMDiffOn_torsionInner_section (I := I) (E := E) hu hcov hτ hσ
  have htorsσυ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (torsionInnerFunctional (I := I) cov x (σ x) (υ x))) u :=
    contMDiffOn_torsionInner_section (I := I) (E := E) hu hcov hσ hυ
  have htorsυτ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (torsionInnerFunctional (I := I) cov x (υ x) (τ x))) u :=
    contMDiffOn_torsionInner_section (I := I) (E := E) hu hcov hυ hτ
  have htors1 :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 1
        (fun x ↦ TotalSpace.mk' ℝ x
          (torsionInnerFunctional (I := I) cov x (τ x) (σ x) (υ x))) u := by
    simpa using htorsτσ.clm_bundle_apply hυ₁
  have htors2 :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 1
        (fun x ↦ TotalSpace.mk' ℝ x
          (torsionInnerFunctional (I := I) cov x (σ x) (υ x) (τ x))) u := by
    simpa using htorsσυ.clm_bundle_apply hτ₁
  have htors3 :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 1
        (fun x ↦ TotalSpace.mk' ℝ x
          (torsionInnerFunctional (I := I) cov x (υ x) (τ x) (σ x))) u := by
    simpa using htorsυτ.clm_bundle_apply hσ₁
  have hsum :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 1
        (fun x ↦ TotalSpace.mk' ℝ x
          (cov.metricDefect x (σ x) (υ x) (τ x) +
            cov.metricDefect x (τ x) (υ x) (σ x) -
            cov.metricDefect x (τ x) (σ x) (υ x) -
            torsionInnerFunctional (I := I) cov x (τ x) (σ x) (υ x) +
            torsionInnerFunctional (I := I) cov x (σ x) (υ x) (τ x) -
            torsionInnerFunctional (I := I) cov x (υ x) (τ x) (σ x))) u := by
    exact ((((hterm1.add_section hterm2).sub_section hterm3).sub_section htors1).add_section
      htors2).sub_section htors3
  have hcorrectionSection :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 1
        (fun x ↦ TotalSpace.mk' ℝ x (correctionFunctional cov x (σ x) (τ x) (υ x))) u := by
    have hscaled :
        ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 1
          (fun x ↦ TotalSpace.mk' ℝ x
            ((1 / 2 : ℝ) *
              (cov.metricDefect x (σ x) (υ x) (τ x) +
                cov.metricDefect x (τ x) (υ x) (σ x) -
                cov.metricDefect x (τ x) (σ x) (υ x) -
                torsionInnerFunctional (I := I) cov x (τ x) (σ x) (υ x) +
                torsionInnerFunctional (I := I) cov x (σ x) (υ x) (τ x) -
                torsionInnerFunctional (I := I) cov x (υ x) (τ x) (σ x)))) u := by
      simpa [Pi.smul_apply, smul_eq_mul] using contMDiffOn_const.smul_section hsum
    refine ContMDiffOn.congr hscaled ?_
    intro x hx
    simp [correctionFunctional_apply, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  exact
    ((eLine.contMDiffOn_section_iff (IB := I) (n := (1 : WithTop ℕ∞))
      (s := fun x ↦ correctionFunctional cov x (σ x) (τ x) (υ x)) (a := u) hu
      (by
        intro x hx
        change x ∈ (Bundle.Trivial.trivialization M ℝ).baseSet
        simp [Bundle.Trivial.trivialization])).mp hcorrectionSection)

theorem contMDiffOn_correctionFunctional_section
    [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun u)
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)) u)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (correctionFunctional cov x (σ x) (τ x))) u := by
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  let eStar :
      Trivialization (E →L[ℝ] ℝ)
        (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) TStar → M) :=
    e.continuousLinearMap (σ := RingHom.id ℝ) eLine
  let corrSec : Π x : M, TStar x := fun x ↦ correctionFunctional cov x (σ x) (τ x)
  have huStar : u ⊆ eStar.baseSet := by
    intro x hx
    simp [eStar, eLine, hu' hx]
  have hcoeff :
      ∀ i, ContMDiffOn I 𝓘(ℝ) 1
        ((LinearMap.piApply (eStar.localFrameCoeff I (continuousDualBasis b) i)) corrSec) u := by
    intro i
    have hframe :
        ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
          (fun y ↦ TotalSpace.mk' E y (e.localFrame b i y)) u :=
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
        (n := (2 : WithTop ℕ∞)) (b := b) i).mono hu'
    have happly :
        ContMDiffOn I 𝓘(ℝ) 1
          (fun x ↦ correctionFunctional cov x (σ x) (τ x) (e.localFrame b i x)) u :=
      contMDiffOn_correctionFunctional_apply_section (I := I) (E := E) hu hcov hσ hτ hframe
    refine ContMDiffOn.congr happly ?_
    intro x hx
    have hxE : x ∈ e.baseSet := hu' hx
    have hxStar : x ∈ eStar.baseSet := huStar hx
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE,
      show ((LinearMap.piApply (eStar.localFrameCoeff I (continuousDualBasis b) i)) corrSec) x =
          eStar.localFrameCoeff I (continuousDualBasis b) i x (corrSec x) by rfl,
      Bundle.Trivialization.localFrameCoeff_eq_coeff
        (I := I) (e := eStar) (b := continuousDualBasis b) (s := corrSec) (hxe := hxStar) (i := i),
      continuousDualBasis_repr]
    simp [corrSec, eStar, eLine, Bundle.Trivialization.continuousLinearMap_apply,
      Bundle.Trivialization.basisAt, correctionFunctional_apply, hxE, hxStar]
  have hsStar :
      IsLocalFrameOn I (E →L[ℝ] ℝ) 1 (eStar.localFrame (continuousDualBasis b)) u :=
    (eStar.isLocalFrameOn_localFrame_baseSet I 1 (continuousDualBasis b)).mono huStar
  have hcoeffStar :
      ∀ i, ContMDiffOn I 𝓘(ℝ) 1 ((LinearMap.piApply (hsStar.coeff i)) corrSec) u := by
    intro i
    refine (hcoeff i).congr ?_
    intro x hx
    have hbasis :
        hsStar.toBasisAt hx = eStar.basisAt (continuousDualBasis b) (huStar hx) := by
      ext j
      simp [hsStar, IsLocalFrameOn.toBasisAt, Bundle.Trivialization.localFrame,
        Bundle.Trivialization.basisAt, huStar hx]
    change hsStar.coeff i x (corrSec x) =
      eStar.localFrameCoeff I (continuousDualBasis b) i x (corrSec x)
    rw [IsLocalFrameOn.coeff_apply_of_mem (hs := hsStar) hx corrSec i,
      Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
        (I := I) (e := eStar) (b := continuousDualBasis b) (hx := huStar hx)
        (s := corrSec) (i := i)]
    simp [hbasis]
  have hωSection :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (corrSec x)) u := by
    exact hsStar.contMDiffOn_of_coeff hcoeffStar
  simpa [corrSec] using hωSection

theorem contMDiffOn_correctionFunctional_localFrame
    [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun u)
    (i j k : ι) :
    ContMDiffOn I 𝓘(ℝ) 1
      (fun x ↦ correctionFunctional cov x
        (e.localFrame b i x) (e.localFrame b j x) (e.localFrame b k x)) u := by
  refine contMDiffOn_correctionFunctional_apply_section (I := I) (E := E) hu hcov ?_ ?_ ?_
  · exact
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
        (n := (2 : WithTop ℕ∞)) (b := b) i).mono hu'
  · exact
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
        (n := (2 : WithTop ℕ∞)) (b := b) j).mono hu'
  · exact
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
        (n := (2 : WithTop ℕ∞)) (b := b) k).mono hu'

theorem contMDiffWithinAt_correctionFunctional_section
    [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun u)
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)) u)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y)) u)
    {x : M} (hx : x ∈ u) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) y
        (correctionFunctional cov y (σ y) (τ y))) u x := by
  have hsection :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) y
          (correctionFunctional cov y (σ y) (τ y))) u :=
    contMDiffOn_correctionFunctional_section (I := I) (E := E) e b hu hu' hcov hσ hτ
  exact hsection x hx

theorem contMDiffAt_correctionFunctional_section
    [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun u)
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)) u)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y)) u)
    {x : M} (hx : x ∈ u) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) y
        (correctionFunctional cov y (σ y) (τ y))) x := by
  have hsection :
      ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) y
          (correctionFunctional cov y (σ y) (τ y))) u x :=
    contMDiffWithinAt_correctionFunctional_section (I := I) (E := E)
      e b hu hu' hcov hσ hτ hx
  exact hsection.contMDiffAt (hu.mem_nhds hx)

noncomputable def localFrameGramMatrix
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} (b : Module.Basis ι ℝ E) (x : M) : ι → ι → ℝ :=
  fun i j ↦ ⟪e.localFrame b i x, e.localFrame b j x⟫

theorem contMDiffOn_inner_localFrame_localFrame
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet) (i j : ι) :
    ContMDiffOn I 𝓘(ℝ) 2 (fun x ↦ ⟪e.localFrame b i x, e.localFrame b j x⟫) u := by
  have hi :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun x ↦ TotalSpace.mk' E x (e.localFrame b i x)) u :=
    (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
      (n := (2 : WithTop ℕ∞)) (b := b) i).mono hu'
  have hj :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun x ↦ TotalSpace.mk' E x (e.localFrame b j x)) u :=
    (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
      (n := (2 : WithTop ℕ∞)) (b := b) j).mono hu'
  exact ContMDiffOn.inner_bundle (IM := I) (IB := I) (F := E) (E := TM) hi hj

theorem contMDiffOn_localFrameGramMatrix
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet) :
    ContMDiffOn I 𝓘(ℝ, ι → ι → ℝ) 2 (localFrameGramMatrix (I := I) e b) u := by
  rw [contMDiffOn_pi_space]
  intro i
  rw [contMDiffOn_pi_space]
  intro j
  simpa [localFrameGramMatrix] using
    contMDiffOn_inner_localFrame_localFrame (I := I) (E := E) e b hu hu' i j

private theorem contDiff_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContDiff ℝ 2 (fun A : ι → ι → ℝ => Matrix.det (show Matrix ι ι ℝ from A)) := by
  classical
  let f : (ι → ι → ℝ) → ℝ :=
    fun A => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i
  have hf : ContDiff ℝ 2 f := by
    rw [contDiff_iff_contDiffAt]
    intro A
    refine ContDiffAt.sum ?_
    intro σ hσ
    refine (contDiffAt_const : ContDiffAt ℝ 2
      (fun _ : ι → ι → ℝ => ((Equiv.Perm.sign σ : ℤ) : ℝ)) A).mul ?_
    refine contDiffAt_prod ?_
    intro i hi
    simpa using
      (contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) (n := (2 : WithTop ℕ∞)) (i := σ i) (j := i)).contDiffAt
  have hEq : f = fun A : ι → ι → ℝ => Matrix.det (show Matrix ι ι ℝ from A) := by
    funext A
    symm
    simpa using (Matrix.det_apply' (show Matrix ι ι ℝ from A))
  simpa [hEq] using hf

private theorem contDiff_matrix_updateRow {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    ContDiff ℝ 2
      (fun A : ι → ι → ℝ =>
        (show ι → ι → ℝ from Matrix.updateRow (show Matrix ι ι ℝ from A) j (Pi.single i (1 : ℝ)))) := by
  classical
  rw [contDiff_pi]
  intro k
  change ContDiff ℝ 2 (fun A : ι → ι → ℝ => Function.update A j (Pi.single i (1 : ℝ)) k)
  by_cases hk : k = j
  · subst hk
    simpa [Function.update] using
      (contDiff_const : ContDiff ℝ 2 (fun _ : ι → ι → ℝ => (Pi.single i (1 : ℝ) : ι → ℝ)))
  · simpa [Function.update, hk] using
      (contDiff_apply (𝕜 := ℝ) (E := ι → ℝ) (n := (2 : WithTop ℕ∞)) (i := k))

private theorem contDiff_matrix_adjugate {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContDiff ℝ 2
      (fun A : ι → ι → ℝ => (show ι → ι → ℝ from Matrix.adjugate (show Matrix ι ι ℝ from A))) := by
  classical
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  change ContDiff ℝ 2 (fun A : ι → ι → ℝ => Matrix.adjugate (Matrix.of A) i j)
  have hEq :
      (fun A : ι → ι → ℝ => Matrix.adjugate (Matrix.of A) i j) =
        (fun A : ι → ι → ℝ => ((Matrix.of A).updateRow j (Pi.single i (1 : ℝ))).det) := by
    funext A
    exact Matrix.adjugate_apply (Matrix.of A) i j
  rw [hEq]
  convert (contDiff_matrix_det (ι := ι)).comp
    (contDiff_matrix_updateRow (ι := ι) i j) using 1 <;> rfl

theorem contMDiffOn_localFrameGramMatrix_det
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet) :
    ContMDiffOn I 𝓘(ℝ) 2
      (fun x => Matrix.det (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)) u := by
  intro x hx
  have h := (contDiff_matrix_det (ι := ι)).comp_contMDiffWithinAt
    (contMDiffOn_localFrameGramMatrix (I := I) (E := E) e b hu hu' x hx)
  exact ContMDiffWithinAt.congr h (by
    intro y hy
    rfl) (by rfl)

theorem localFrameGramMatrix_pos
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) {c : ι → ℝ} (hc : c ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j * localFrameGramMatrix (I := I) e b x i j := by
  classical
  let v : TM x := ∑ i, c i • e.localFrame b i x
  have hv : v ≠ 0 := by
    intro hv0
    apply hc
    calc
      c = (e.basisAt b hx).repr v := by
        simpa [v, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hx] using
          ((e.basisAt b hx).repr_sum_self c).symm
      _ = 0 := by simpa [hv0]
  have hsum :
      ⟪v, v⟫ =
        ∑ i, ∑ j, c i * c j * localFrameGramMatrix (I := I) e b x i j := by
    simp_rw [v, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      localFrameGramMatrix, mul_assoc]
  calc
    0 < ‖v‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    _ = ⟪v, v⟫ := by simpa using (real_inner_self_eq_norm_sq v).symm
    _ = ∑ i, ∑ j, c i * c j * localFrameGramMatrix (I := I) e b x i j := hsum

theorem localFrameGramMatrix_det_ne_zero
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) :
    (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x).det ≠ 0 := by
  let A : Matrix ι ι ℝ := localFrameGramMatrix (I := I) e b x
  intro hA
  obtain ⟨c, hc, hAc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
  have hAcA : A.mulVec c = 0 := by
    simpa [A] using hAc
  have hAc' : ∀ i, ∑ j, A i j * c j = 0 := by
    intro i
    have hi := congrFun hAcA i
    simpa [Matrix.mulVec, dotProduct] using hi
  have hsum :
      ∑ i, ∑ j, c i * c j * localFrameGramMatrix (I := I) e b x i j = 0 := by
    calc
      ∑ i, ∑ j, c i * c j * localFrameGramMatrix (I := I) e b x i j
          = ∑ i, c i * (∑ j, A i j * c j) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [A, mul_assoc, mul_left_comm, mul_comm]
      _ = ∑ i, c i * 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hAc' i]
      _ = 0 := by simp
  have hpos := localFrameGramMatrix_pos (I := I) (E := E) e b hx hc
  rw [hsum] at hpos
  linarith

/-- On a compact subset of a local trivialization base, the local-frame Gram determinant is
uniformly bounded away from zero. -/
theorem localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set M} (hK : IsCompact K) (hKbase : K ⊆ e.baseSet) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x : M⦄, x ∈ K →
      δ ≤ ‖(show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x).det‖ := by
  let f : M → ℝ :=
    fun x => (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x).det
  have hf_base : ContinuousOn f e.baseSet := by
    simpa [f] using
      (contMDiffOn_localFrameGramMatrix_det (I := I) (E := E) e b
        e.open_baseSet (subset_refl e.baseSet)).continuousOn
  have hfK : ContinuousOn f K := hf_base.mono hKbase
  by_cases hKnonempty : K.Nonempty
  · have hnorm : ContinuousOn (fun x => ‖f x‖) K := hfK.norm
    rcases hK.exists_isMinOn hKnonempty hnorm with ⟨x₀, hx₀, hmin⟩
    refine ⟨‖f x₀‖, ?_, ?_⟩
    · exact norm_pos_iff.mpr
        (localFrameGramMatrix_det_ne_zero (I := I) (E := E) e b (hKbase hx₀))
    · intro x hx
      exact (isMinOn_iff.mp hmin) x hx
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact False.elim (hKnonempty ⟨x, hx⟩)

/-- On a compact time-space set whose spatial projection lies in a local trivialization base, the
local-frame Gram determinant is uniformly bounded away from zero. -/
theorem localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃z : ℝ × M⦄, z ∈ K →
      δ ≤ ‖(show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b z.2).det‖ := by
  let Kspace : Set M := Prod.snd '' K
  have hKspace : IsCompact Kspace := hK.image continuous_snd
  have hKspaceBase : Kspace ⊆ e.baseSet := by
    rintro x ⟨z, hz, rfl⟩
    exact hKbase hz
  rcases localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_isCompact
      (I := I) (E := E) e b hKspace hKspaceBase with
    ⟨δ, hδpos, hδ⟩
  exact ⟨δ, hδpos, fun z hz => hδ ⟨z, hz, rfl⟩⟩

theorem localFrameGramMatrix_isUnit_det
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) :
    IsUnit (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x).det :=
  isUnit_iff_ne_zero.mpr (localFrameGramMatrix_det_ne_zero (I := I) (E := E) e b hx)

theorem contMDiffOn_localFrameGramMatrix_det_inv
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet) :
    ContMDiffOn I 𝓘(ℝ) 2
      (fun x => (Matrix.det (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x))⁻¹) u :=
  (contMDiffOn_localFrameGramMatrix_det (I := I) (E := E) e b hu hu').inv₀
    (fun x hx => localFrameGramMatrix_det_ne_zero (I := I) (E := E) e b (hu' hx))

theorem contMDiffOn_localFrameGramMatrix_adjugate
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet) :
    ContMDiffOn I 𝓘(ℝ, ι → ι → ℝ) 2
      (fun x =>
        (show ι → ι → ℝ from
          Matrix.adjugate (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x))) u := by
  intro x hx
  have h := (contDiff_matrix_adjugate (ι := ι)).comp_contMDiffWithinAt
    (contMDiffOn_localFrameGramMatrix (I := I) (E := E) e b hu hu' x hx)
  exact ContMDiffWithinAt.congr h (by
    intro y hy
    rfl) (by rfl)

theorem contMDiffOn_localFrameGramMatrix_inv
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet) :
    ContMDiffOn I 𝓘(ℝ, ι → ι → ℝ) 2
      (fun x =>
        (show ι → ι → ℝ from
          (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ)))) u := by
  refine ContMDiffOn.congr
    ((contMDiffOn_localFrameGramMatrix_det_inv (I := I) (E := E) e b hu hu').smul
      (contMDiffOn_localFrameGramMatrix_adjugate (I := I) (E := E) e b hu hu')) ?_
  intro x hx
  change (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ =
    ((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x).det)⁻¹ •
      Matrix.adjugate (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)
  rw [Matrix.inv_def, Ring.inverse_eq_inv]

noncomputable def rieszMap (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x :=
  (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma rieszMap_apply_inner (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) (w : TangentSpace I x) :
    ⟪rieszMap (I := I) x φ, w⟫ = φ w := by
  change ⟪(InnerProductSpace.toDual ℝ (TangentSpace I x)).symm φ, w⟫ = φ w
  exact InnerProductSpace.toDual_symm_apply

lemma localFrameCoeff_rieszMap
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {omega : Π x : M, TStar x} {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    e.localFrameCoeff I b i x (rieszMap (I := I) x (omega x)) =
      ∑ j,
        (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ) i j) *
          omega x (e.localFrame b j x) := by
  classical
  let A : Matrix ι ι ℝ := localFrameGramMatrix (I := I) e b x
  let basis := e.basisAt b hx
  let v : TM x := rieszMap (I := I) x (omega x)
  let c : ι → ℝ := basis.repr v
  have hAc : A.mulVec c = fun j => omega x (e.localFrame b j x) := by
    ext j
    calc
      (A.mulVec c) j = ∑ k, A j k * c k := by
        simp [Matrix.mulVec, dotProduct]
      _ = ∑ k, c k * A k j := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        simp [A, localFrameGramMatrix, real_inner_comm, mul_comm]
      _ = ∑ k, c k * ⟪basis k, basis j⟫ := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        simp [A, basis, localFrameGramMatrix,
          Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hx]
      _ = ∑ k, ⟪c k • basis k, basis j⟫ := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        simp [real_inner_smul_left]
      _ = ⟪∑ k, c k • basis k, basis j⟫ := by
        rw [← sum_inner]
      _ = ⟪v, basis j⟫ := by
        rw [basis.sum_repr v]
      _ = omega x (basis j) := by
        simp [v, rieszMap_apply_inner]
      _ = omega x (e.localFrame b j x) := by
        simp [basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hx]
  have hAunit : IsUnit A.det := by
    simpa [A] using localFrameGramMatrix_isUnit_det (I := I) (E := E) e b hx
  have hc :
      c = A⁻¹.mulVec (fun j => omega x (e.localFrame b j x)) := by
    calc
      c = (1 : Matrix ι ι ℝ).mulVec c := by simp
      _ = (A⁻¹ * A).mulVec c := by rw [Matrix.nonsing_inv_mul A hAunit]
      _ = A⁻¹.mulVec (A.mulVec c) := by rw [Matrix.mulVec_mulVec]
      _ = A⁻¹.mulVec (fun j => omega x (e.localFrame b j x)) := by rw [hAc]
  have hci :
      c i =
        ∑ j, (A⁻¹) i j * omega x (e.localFrame b j x) := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hc i
  calc
    e.localFrameCoeff I b i x (rieszMap (I := I) x (omega x))
        = c i := by
            simpa [v, c] using
              (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
                (I := I) (e := e) (b := b) (hx := hx)
                (s := fun y => rieszMap (I := I) y (omega y)) (i := i))
    _ = ∑ j, (A⁻¹) i j * omega x (e.localFrame b j x) := hci
    _ = ∑ j,
          (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ) i j) *
            omega x (e.localFrame b j x) := by
              simp [A]

theorem contMDiffOn_rieszMap_section
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    {omega : Π x : M, TStar x}
    (hω : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      1 (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (omega x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (rieszMap (I := I) x (omega x))) u := by
  classical
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  let eStar :
      Trivialization (E →L[ℝ] ℝ)
        (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) TStar → M) :=
    e.continuousLinearMap (σ := RingHom.id ℝ) eLine
  have huStar : u ⊆ eStar.baseSet := by
    intro x hx
    simp [eStar, eLine, hu' hx]
  have hωcoeff :
      ∀ j, ContMDiffOn I 𝓘(ℝ) 1 (fun x ↦ omega x (e.localFrame b j x)) u := by
    intro j
    have hj :
        ContMDiffOn I 𝓘(ℝ) 1
          ((LinearMap.piApply (eStar.localFrameCoeff I (continuousDualBasis b) j)) omega) u :=
      contMDiffOn_localFrameCoeff
        (I := I) (e := eStar) (b := continuousDualBasis b) hu huStar hω j
    refine ContMDiffOn.congr hj ?_
    intro x hx
    have hxE : x ∈ e.baseSet := hu' hx
    have hxStar : x ∈ eStar.baseSet := huStar hx
    rw [show ((LinearMap.piApply (eStar.localFrameCoeff I (continuousDualBasis b) j)) omega) x =
        eStar.localFrameCoeff I (continuousDualBasis b) j x (omega x) by rfl,
      Bundle.Trivialization.localFrameCoeff_eq_coeff
        (I := I) (e := eStar) (b := continuousDualBasis b) (s := omega) (hxe := hxStar) (i := j),
      continuousDualBasis_repr]
    simp [eStar, eLine, Bundle.Trivialization.continuousLinearMap_apply,
      Bundle.Trivialization.basisAt, hxE, hxStar]
  have hInvEntry :
      ∀ i j, ContMDiffOn I 𝓘(ℝ) 1
        (fun x =>
          (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ) i j)) u := by
    intro i j
    have hInv := contMDiffOn_localFrameGramMatrix_inv (I := I) (E := E) e b hu hu'
    rw [contMDiffOn_pi_space] at hInv
    have hi := hInv i
    rw [contMDiffOn_pi_space] at hi
    exact (hi j).of_le (by norm_num)
  have hcoeff :
      ∀ i, ContMDiffOn I 𝓘(ℝ) 1
        ((LinearMap.piApply (e.localFrameCoeff I b i))
          (fun x => rieszMap (I := I) x (omega x))) u := by
    intro i
    have hsum :
        ∀ s : Finset ι,
          ContMDiffOn I 𝓘(ℝ) 1
            (fun x => s.sum fun j =>
              (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ) i j) *
                omega x (e.localFrame b j x)) u := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simpa using (contMDiffOn_const :
          ContMDiffOn I 𝓘(ℝ) 1 (fun _ : M => (0 : ℝ)) u)
      · intro j s hj hs
        have hfirst :
            ContMDiffOn I 𝓘(ℝ) 1
              (fun x =>
                (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ) i j) *
                  omega x (e.localFrame b j x)) u :=
          (hInvEntry i j).mul (hωcoeff j)
        have hadd :
            ContMDiffOn I 𝓘(ℝ) 1
              (fun x =>
                (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ) i j) *
                    omega x (e.localFrame b j x) +
                  s.sum (fun j' =>
                    (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ :
                        Matrix ι ι ℝ) i j') *
                      omega x (e.localFrame b j' x))) u :=
          hfirst.add hs
        refine ContMDiffOn.congr hadd ?_
        intro x hx
        simp [Finset.sum_insert, hj, add_assoc, add_comm, add_left_comm]
    refine ContMDiffOn.congr (hsum Finset.univ) ?_
    intro x hx
    simpa using
      (localFrameCoeff_rieszMap (I := I) (E := E) (e := e) (b := b)
        (omega := omega) (hx := hu' hx) (i := i))
  exact (contMDiffOn_iff_localFrameCoeff
    (I := I) (e := e) (b := b)
    (s := fun x => rieszMap (I := I) x (omega x)) (t := u) (k := (1 : WithTop ℕ∞)) hu hu').2 hcoeff

/-- The one-form correcting an arbitrary affine connection to the Levi-Civita connection. -/
noncomputable def leviCivitaCorrection (cov : CovariantDerivative I E TM) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  ((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x →L[ℝ] ℝ)
      (TangentSpace I x)) (rieszMap (I := I) x)).comp (correctionFunctional cov x)

@[simp] lemma leviCivitaCorrection_apply (cov : CovariantDerivative I E TM) (x : M)
    (v u : TangentSpace I x) :
    cov.leviCivitaCorrection x v u = rieszMap (I := I) x (correctionFunctional cov x v u) := by
  rfl

theorem contMDiffOn_leviCivitaCorrection_apply_section
    [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun u)
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)) u)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (cov.leviCivitaCorrection x (σ x) (τ x))) u := by
  have hcorr :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (correctionFunctional cov x (σ x) (τ x))) u :=
    contMDiffOn_correctionFunctional_section (I := I) (E := E) e b hu hu' hcov hσ hτ
  simpa [CovariantDerivative.leviCivitaCorrection_apply] using
    contMDiffOn_rieszMap_section (I := I) (E := E) (e := e) (b := b) hu hu' hcorr

theorem contMDiffOn_leviCivitaCorrection_partial_section
    [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun u)
    {σ : Π y : M, TangentSpace I y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x
        (cov.leviCivitaCorrection x (σ x))) u := by
  classical
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  let eStar :
      Trivialization (E →L[ℝ] ℝ)
        (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) TStar → M) :=
    e.continuousLinearMap (σ := RingHom.id ℝ) eLine
  have huStar : u ⊆ eStar.baseSet := by
    intro x hx
    simp [eStar, eLine, hu' hx]
  have hdual :
      ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (eStar.localFrame (continuousDualBasis b) i x)) u := by
    intro i
    exact
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := eStar)
        (n := (1 : WithTop ℕ∞)) (b := continuousDualBasis b) i).mono huStar
  have hvalue :
      ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun x ↦ TotalSpace.mk' E x
          (cov.leviCivitaCorrection x (σ x) (e.localFrame b i x))) u := by
    intro i
    have hframe :
        ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
          (fun x ↦ TotalSpace.mk' E x (e.localFrame b i x)) u :=
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
        (n := (2 : WithTop ℕ∞)) (b := b) i).mono hu'
    exact contMDiffOn_leviCivitaCorrection_apply_section (I := I) (E := E) e b hu hu' hcov hσ
      hframe
  have hsum :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x
          (∑ i,
            (eStar.localFrame (continuousDualBasis b) i x).smulRight
              (cov.leviCivitaCorrection x (σ x) (e.localFrame b i x)))) u := by
    simpa using
      (ContMDiffOn.sum_section (s := (Finset.univ : Finset ι)) fun i hi ↦
        ContMDiffOn.smulRightSection (I := I) (V := TM) hu (hdual i) (hvalue i))
  refine ContMDiffOn.congr hsum ?_
  intro x hx
  have hxE : x ∈ e.baseSet := hu' hx
  have hxStar : x ∈ eStar.baseSet := huStar hx
  apply congrArg (fun A ↦ TotalSpace.mk' (E := TEnd) (E →L[ℝ] E) x A)
  ext v
  let basis := e.basisAt b hxE
  let s : Π y : M, TM y := fun y ↦ ∑ j, basis.repr v j • e.localFrame b j y
  have hsx : s x = v := by
    simpa [s, basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      using basis.sum_repr v
  have hcoeff_v : ∀ i, e.localFrameCoeff I b i x v = basis.repr v i := by
    intro i
    calc
      e.localFrameCoeff I b i x v = e.localFrameCoeff I b i x (s x) := by rw [hsx]
      _ = basis.repr (s x) i := by
            simpa [basis] using
              (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
                (I := I) (e := e) (b := b) (hx := hxE) (s := s) (i := i))
      _ = basis.repr v i := by rw [hsx]
  have hdual_basis :
      ∀ i j,
        eStar.localFrame (continuousDualBasis b) i x (e.localFrame b j x) = if i = j then 1 else 0 := by
    intro i j
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := eStar) (b := continuousDualBasis b) hxStar,
      Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
    simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
    rw [Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply]
    rw [← Bundle.Trivialization.symmL_apply (R := ℝ) e hxE]
    have hsymm :
        eStar.symm x ((continuousDualBasis b) i) =
          (eLine.symmL ℝ x).comp (((continuousDualBasis b) i).comp (e.continuousLinearMapAt ℝ x)) := by
      change
        (Bundle.Pretrivialization.continuousLinearMap (RingHom.id ℝ) e eLine).symm x
            ((continuousDualBasis b) i) =
          (eLine.symmL ℝ x).comp
            (((continuousDualBasis b) i).comp (e.continuousLinearMapAt ℝ x))
      simpa [eLine] using
        (Bundle.Pretrivialization.continuousLinearMap_symm_apply'
          (σ := RingHom.id ℝ) (e₁ := e) (e₂ := eLine) (b := x)
          (hb := ⟨hxE, by simp [eLine]⟩) ((continuousDualBasis b) i))
    rw [hsymm]
    simp only [ContinuousLinearMap.comp_apply]
    rw [Bundle.Trivialization.continuousLinearMapAt_symmL (e := e) (R := ℝ) (hb := hxE)]
    simpa [eLine, continuousDualBasis, Finsupp.single_apply, eq_comm]
  have hdual_apply :
      ∀ i, eStar.localFrame (continuousDualBasis b) i x v = e.localFrameCoeff I b i x v := by
    intro i
    calc
      eStar.localFrame (continuousDualBasis b) i x v
          = eStar.localFrame (continuousDualBasis b) i x (∑ j, basis.repr v j • basis j) := by
              rw [basis.sum_repr v]
      _ = ∑ j, basis.repr v j * eStar.localFrame (continuousDualBasis b) i x (basis j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [map_smul]
            simp [smul_eq_mul]
      _ = ∑ j, basis.repr v j * (if i = j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa [basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
              using congrArg (fun r : ℝ ↦ basis.repr v j * r) (hdual_basis i j)
      _ = basis.repr v i := by simp
      _ = e.localFrameCoeff I b i x v := by rw [hcoeff_v i]
  have hdecomp :
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x = v := by
    calc
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x
          = ∑ i, e.localFrameCoeff I b i x v • e.localFrame b i x := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hdual_apply i]
      _ = ∑ i, basis.repr v i • basis i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [basis, hcoeff_v i,
              Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      _ = v := by simpa using basis.sum_repr v
  have hmap :
      (cov.leviCivitaCorrection x (σ x))
          (∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x) =
        ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v •
          cov.leviCivitaCorrection x (σ x) (e.localFrame b i x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [map_smul]
  calc
    cov.leviCivitaCorrection x (σ x) v
        = (cov.leviCivitaCorrection x (σ x))
            (∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x) := by
              rw [hdecomp]
    _ = ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v •
          cov.leviCivitaCorrection x (σ x) (e.localFrame b i x) := by
            rw [hmap]
    _ = (∑ i,
          (eStar.localFrame (continuousDualBasis b) i x).smulRight
            (cov.leviCivitaCorrection x (σ x) (e.localFrame b i x))) v := by
          simp [ContinuousLinearMap.smulRight_apply]

theorem contMDiffOn_leviCivitaCorrection_section
    [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E) (E := TCorr) x
        (cov.leviCivitaCorrection x)) u := by
  classical
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  let eStar :
      Trivialization (E →L[ℝ] ℝ)
        (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) TStar → M) :=
    e.continuousLinearMap (σ := RingHom.id ℝ) eLine
  have huStar : u ⊆ eStar.baseSet := by
    intro x hx
    simp [eStar, eLine, hu' hx]
  have hdual :
      ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (eStar.localFrame (continuousDualBasis b) i x)) u := by
    intro i
    exact
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := eStar)
        (n := (1 : WithTop ℕ∞)) (b := continuousDualBasis b) i).mono huStar
  have hvalue :
      ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x
          (cov.leviCivitaCorrection x (e.localFrame b i x))) u := by
    intro i
    have hframe :
        ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
          (fun x ↦ TotalSpace.mk' E x (e.localFrame b i x)) u :=
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
        (n := (2 : WithTop ℕ∞)) (b := b) i).mono hu'
    exact contMDiffOn_leviCivitaCorrection_partial_section (I := I) (E := E) e b hu hu' hcov
      hframe
  have hsum :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E) (E := TCorr) x
          (∑ i,
            (eStar.localFrame (continuousDualBasis b) i x).smulRight
              (cov.leviCivitaCorrection x (e.localFrame b i x)))) u := by
    simpa using
      (ContMDiffOn.sum_section (s := (Finset.univ : Finset ι)) fun i hi ↦
        ContMDiffOn.smulRightSection (I := I) (V := TEnd) hu (hdual i) (hvalue i))
  refine ContMDiffOn.congr hsum ?_
  intro x hx
  have hxE : x ∈ e.baseSet := hu' hx
  have hxStar : x ∈ eStar.baseSet := huStar hx
  apply congrArg (fun A ↦ TotalSpace.mk' (E := TCorr) (E →L[ℝ] E →L[ℝ] E) x A)
  ext v u
  let basis := e.basisAt b hxE
  let s : Π y : M, TM y := fun y ↦ ∑ j, basis.repr v j • e.localFrame b j y
  have hsx : s x = v := by
    simpa [s, basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      using basis.sum_repr v
  have hcoeff_v : ∀ i, e.localFrameCoeff I b i x v = basis.repr v i := by
    intro i
    calc
      e.localFrameCoeff I b i x v = e.localFrameCoeff I b i x (s x) := by rw [hsx]
      _ = basis.repr (s x) i := by
            simpa [basis] using
              (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
                (I := I) (e := e) (b := b) (hx := hxE) (s := s) (i := i))
      _ = basis.repr v i := by rw [hsx]
  have hdual_basis :
      ∀ i j,
        eStar.localFrame (continuousDualBasis b) i x (e.localFrame b j x) = if i = j then 1 else 0 := by
    intro i j
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := eStar) (b := continuousDualBasis b) hxStar,
      Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
    simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
    rw [Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply]
    rw [← Bundle.Trivialization.symmL_apply (R := ℝ) e hxE]
    have hsymm :
        eStar.symm x ((continuousDualBasis b) i) =
          (eLine.symmL ℝ x).comp (((continuousDualBasis b) i).comp (e.continuousLinearMapAt ℝ x)) := by
      change
        (Bundle.Pretrivialization.continuousLinearMap (RingHom.id ℝ) e eLine).symm x
            ((continuousDualBasis b) i) =
          (eLine.symmL ℝ x).comp
            (((continuousDualBasis b) i).comp (e.continuousLinearMapAt ℝ x))
      simpa [eLine] using
        (Bundle.Pretrivialization.continuousLinearMap_symm_apply'
          (σ := RingHom.id ℝ) (e₁ := e) (e₂ := eLine) (b := x)
          (hb := ⟨hxE, by simp [eLine]⟩) ((continuousDualBasis b) i))
    rw [hsymm]
    simp only [ContinuousLinearMap.comp_apply]
    rw [Bundle.Trivialization.continuousLinearMapAt_symmL (e := e) (R := ℝ) (hb := hxE)]
    simpa [eLine, continuousDualBasis, Finsupp.single_apply, eq_comm]
  have hdual_apply :
      ∀ i, eStar.localFrame (continuousDualBasis b) i x v = e.localFrameCoeff I b i x v := by
    intro i
    calc
      eStar.localFrame (continuousDualBasis b) i x v
          = eStar.localFrame (continuousDualBasis b) i x (∑ j, basis.repr v j • basis j) := by
              rw [basis.sum_repr v]
      _ = ∑ j, basis.repr v j * eStar.localFrame (continuousDualBasis b) i x (basis j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [map_smul]
            simp [smul_eq_mul]
      _ = ∑ j, basis.repr v j * (if i = j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa [basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
              using congrArg (fun r : ℝ ↦ basis.repr v j * r) (hdual_basis i j)
      _ = basis.repr v i := by simp
      _ = e.localFrameCoeff I b i x v := by rw [hcoeff_v i]
  have hdecomp :
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x = v := by
    calc
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x
          = ∑ i, e.localFrameCoeff I b i x v • e.localFrame b i x := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hdual_apply i]
      _ = ∑ i, basis.repr v i • basis i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [basis, hcoeff_v i,
              Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      _ = v := by simpa using basis.sum_repr v
  have hmap :
      (cov.leviCivitaCorrection x)
          (∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x) =
        ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v •
          cov.leviCivitaCorrection x (e.localFrame b i x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [map_smul]
  calc
    cov.leviCivitaCorrection x v u
        = ((cov.leviCivitaCorrection x)
            (∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x)) u := by
              rw [hdecomp]
    _ = (∑ i, (eStar.localFrame (continuousDualBasis b) i x) v •
          cov.leviCivitaCorrection x (e.localFrame b i x)) u := by
            exact congrArg (fun A : TEnd x ↦ A u) hmap
    _ = ((∑ i,
          (eStar.localFrame (continuousDualBasis b) i x).smulRight
            (cov.leviCivitaCorrection x (e.localFrame b i x))) v) u := by
          simp [ContinuousLinearMap.smulRight_apply]

lemma leviCivitaCorrection_inner (cov : CovariantDerivative I E TM) (x : M)
    (v u w : TangentSpace I x) :
    2 * ⟪cov.leviCivitaCorrection x v u, w⟫ =
      cov.metricDefect x v w u + cov.metricDefect x u w v - cov.metricDefect x u v w -
        ⟪cov.torsion x u v, w⟫ + ⟪cov.torsion x v w, u⟫ - ⟪cov.torsion x w u, v⟫ := by
  rw [leviCivitaCorrection_apply, rieszMap_apply_inner, correctionFunctional_apply]
  ring_nf

lemma torsion_addOneForm_apply
    (cov : CovariantDerivative I E TM)
    (A : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (x : M) (u v : TangentSpace I x) :
    (CovariantDerivative.addOneForm cov A).torsion x u v =
      cov.torsion x u v + A x v u - A x u v := by
  rw [CovariantDerivative.torsion_apply_eq_extend
      (cov := CovariantDerivative.addOneForm cov A) (x := x) u v]
  rw [CovariantDerivative.torsion_apply_eq_extend (cov := cov) (x := x) u v]
  simp only [CovariantDerivative.addOneForm, ContinuousLinearMap.add_apply, FiberBundle.extend_apply_self]
  abel

lemma metricDefect_addOneForm_apply
    (cov : CovariantDerivative I E TM)
    (A : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (x : M) (u v w : TangentSpace I x) :
    (CovariantDerivative.addOneForm cov A).metricDefect x v w u =
      cov.metricDefect x v w u - ⟪A x v u, w⟫ - ⟪v, A x w u⟫ := by
  rw [metricDefect_apply
      (cov := CovariantDerivative.addOneForm cov A),
    metricDefect_apply (cov := cov)]
  simp only [CovariantDerivative.addOneForm, ContinuousLinearMap.add_apply, FiberBundle.extend_apply_self,
    inner_add_left, inner_add_right]
  ring

lemma leviCivitaCorrection_sub_eq_neg_torsion (cov : CovariantDerivative I E TM) (x : M)
    (u v : TangentSpace I x) :
    cov.leviCivitaCorrection x v u - cov.leviCivitaCorrection x u v = - cov.torsion x u v := by
  apply ext_inner_right ℝ
  intro w
  have h₁ := cov.leviCivitaCorrection_inner x v u w
  have h₂ := cov.leviCivitaCorrection_inner x u v w
  have hD :
      cov.metricDefect x u v w = cov.metricDefect x v u w := by
    simpa using congrArg (fun f ↦ f w) (cov.metricDefect_symm x u v)
  have hT₁ : ⟪cov.torsion x v u, w⟫ = -⟪cov.torsion x u v, w⟫ := by
    rw [cov.torsion_antisymm (x := x) v u]
    simp
  have hT₂ : ⟪cov.torsion x u w, v⟫ = -⟪cov.torsion x w u, v⟫ := by
    rw [cov.torsion_antisymm (x := x) u w]
    simp
  have hT₃ : ⟪cov.torsion x w v, u⟫ = -⟪cov.torsion x v w, u⟫ := by
    rw [cov.torsion_antisymm (x := x) w v]
    simp
  have hscalar :
      ⟪cov.leviCivitaCorrection x v u, w⟫ - ⟪cov.leviCivitaCorrection x u v, w⟫ =
        -⟪cov.torsion x u v, w⟫ := by
    linarith
  have hscalar' :
      ⟪cov.leviCivitaCorrection x v u - cov.leviCivitaCorrection x u v, w⟫ =
        -⟪cov.torsion x u v, w⟫ := by
    simpa [sub_eq_add_neg, inner_add_left, inner_neg_left] using hscalar
  calc
    ⟪cov.leviCivitaCorrection x v u - cov.leviCivitaCorrection x u v, w⟫
        = -⟪cov.torsion x u v, w⟫ := hscalar'
    _ = ⟪-cov.torsion x u v, w⟫ := by rw [inner_neg_left]

lemma correctedConnection_isTorsionFree (cov : CovariantDerivative I E TM) :
    (CovariantDerivative.addOneForm cov cov.leviCivitaCorrection).IsTorsionFree := by
  unfold IsTorsionFree
  ext x u v
  rw [torsion_addOneForm_apply (cov := cov) (A := cov.leviCivitaCorrection)]
  calc
    cov.torsion x u v + cov.leviCivitaCorrection x v u - cov.leviCivitaCorrection x u v
        = cov.torsion x u v +
            (cov.leviCivitaCorrection x v u - cov.leviCivitaCorrection x u v) := by
              abel
    _ = cov.torsion x u v + (-cov.torsion x u v) := by
          rw [leviCivitaCorrection_sub_eq_neg_torsion (cov := cov) (x := x) u v]
    _ = 0 := by abel

lemma correctedConnection_metricDefect_eq_zero (cov : CovariantDerivative I E TM) (x : M)
    (v w : TangentSpace I x) :
    (CovariantDerivative.addOneForm cov cov.leviCivitaCorrection).metricDefect x v w = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.zero_apply]
  have hdef := metricDefect_addOneForm_apply (cov := cov)
    (A := cov.leviCivitaCorrection) x u v w
  have h₁ := cov.leviCivitaCorrection_inner x v u w
  have h₂ : 2 * ⟪v, cov.leviCivitaCorrection x w u⟫ =
      cov.metricDefect x w v u + cov.metricDefect x u v w - cov.metricDefect x u w v -
        ⟪cov.torsion x u w, v⟫ + ⟪cov.torsion x w v, u⟫ - ⟪cov.torsion x v u, w⟫ := by
    simpa [real_inner_comm] using cov.leviCivitaCorrection_inner x w u v
  have hD :
      cov.metricDefect x w v u = cov.metricDefect x v w u := by
    simpa using congrArg (fun f ↦ f u) (cov.metricDefect_symm x w v)
  have hT₁ : ⟪cov.torsion x u w, v⟫ = -⟪cov.torsion x w u, v⟫ := by
    rw [cov.torsion_antisymm (x := x) u w]
    simp
  have hT₂ : ⟪cov.torsion x w v, u⟫ = -⟪cov.torsion x v w, u⟫ := by
    rw [cov.torsion_antisymm (x := x) w v]
    simp
  have hT₃ : ⟪cov.torsion x v u, w⟫ = -⟪cov.torsion x u v, w⟫ := by
    rw [cov.torsion_antisymm (x := x) v u]
    simp
  have hsum :
      ⟪cov.leviCivitaCorrection x v u, w⟫ + ⟪v, cov.leviCivitaCorrection x w u⟫ =
        cov.metricDefect x v w u := by
    linarith
  rw [metricDefect_addOneForm_apply (cov := cov) (A := cov.leviCivitaCorrection)]
  linarith

lemma correctedConnection_isMetricCompatible (cov : CovariantDerivative I E TM) :
    IsMetricCompatibleTangent
      (CovariantDerivative.addOneForm cov cov.leviCivitaCorrection) := by
  exact
    (isMetricCompatibleTangent_iff_metricDefect_eq_zero
      (cov := CovariantDerivative.addOneForm cov cov.leviCivitaCorrection)).mpr
      (fun x v w => cov.correctedConnection_metricDefect_eq_zero x v w)

/-- The Levi-Civita connection obtained by correcting an arbitrary affine connection. -/
noncomputable def leviCivitaConnection (cov : CovariantDerivative I E TM) : CovariantDerivative I E TM :=
  CovariantDerivative.addOneForm cov cov.leviCivitaCorrection

theorem contMDiffCovariantDerivativeOn_leviCivitaConnection
    [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun u) :
    ContMDiffCovariantDerivativeOn E 1 (cov.leviCivitaConnection.toFun) u := by
  simpa [CovariantDerivative.leviCivitaConnection] using
    (ContMDiffCovariantDerivativeOn.addOneForm (I := I) (E := E) (F := E) (V := TM) (n := 1)
      hcov (contMDiffOn_leviCivitaCorrection_section (I := I) (E := E) e b hu hu' hcov))

theorem contMDiffCovariantDerivativeOn_of_contMDiffCovariantDerivative
    [T2Space M] [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 1]
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E 1 cov.toFun u := by
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  have hux : u ∈ nhds x := hu.mem_nhds hx
  obtain ⟨ψ, hψtsupp, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hux).mem_iff.mp hux
  have hψ : ContMDiff I 𝓘(ℝ) 2 ψ := by
    exact ψ.contMDiff.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by decide)
  let τ : Π y : M, TM y := fun y ↦ ψ y • σ y
  have hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (τ y)) := by
    simpa [τ] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E) (V := TM) (u := u)
        (n := (2 : WithTop ℕ∞)) (ψ := ψ) hψ.contMDiffOn hu hψtsupp hσ)
  have hcovτ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) y (cov τ y)) := by
    have hτOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (τ y)) Set.univ := by
      simpa [contMDiffOn_univ] using hτ
    simpa [contMDiffOn_univ] using
      ((inferInstance : ContMDiffCovariantDerivative cov 1).contMDiff.contMDiff hτOn)
  have hψeq1 : {y : M | ψ y = 1} ∈ nhds x := by
    filter_upwards [ψ.eventuallyEq_one] with y hy
    simpa using hy
  rcases mem_nhds_iff.mp hψeq1 with ⟨w, hwsub, hwopen, hxw⟩
  have hwu : w ⊆ u := by
    intro y hy
    have hy1 : ψ y = 1 := hwsub hy
    have hysupp : y ∈ Function.support ψ := by
      simpa [Function.support] using show ψ y ≠ 0 by rw [hy1]; norm_num
    exact hψsupp hysupp
  have hEq : ∀ y ∈ w, cov σ y = cov τ y := by
    intro y hy
    have hyu : y ∈ u := hwu hy
    have hσy : MDiffAt (fun z ↦ TotalSpace.mk' E z (σ z)) y := by
      exact ((((hσ y hyu).contMDiffAt (hu.mem_nhds hyu)).of_le
        (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero)
    have hτy : MDiffAt (fun z ↦ TotalSpace.mk' E z (τ z)) y := by
      exact ((hτ.contMDiffAt.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero)
    exact (cov.isCovariantDerivativeOn (s := w)).congr_of_eqOn hσy hτy (hwopen.mem_nhds hy)
      (fun z hz ↦ by
        have hz1 : ψ z = 1 := hwsub hz
        calc
          σ z = 1 • σ z := by simpa using (one_smul ℝ (σ z)).symm
          _ = ψ z • σ z := by simpa [hz1])
  have hcovσw : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) y (cov σ y)) w := by
    refine ContMDiffOn.congr hcovτ.contMDiffOn ?_
    intro y hy
    exact congrArg (fun A ↦ TotalSpace.mk' (E := TEnd) (E →L[ℝ] E) y A) (hEq y hy)
  refine ⟨w, hwopen, hxw, ?_⟩
  simpa [Set.inter_eq_right.mpr hwu] using hcovσw

theorem contMDiff_leviCivitaCorrection_section
    [T2Space M] [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 1] :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E) (E := TCorr) x
        (cov.leviCivitaCorrection x)) := by
  apply contMDiff_of_locally_contMDiffOn
  intro x
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) := trivializationAt E TM x
  let b := Module.finBasis ℝ E
  refine ⟨e.baseSet, e.open_baseSet, FiberBundle.mem_baseSet_trivializationAt E TM x, ?_⟩
  have hcov :
      ContMDiffCovariantDerivativeOn E 1 cov.toFun e.baseSet :=
    contMDiffCovariantDerivativeOn_of_contMDiffCovariantDerivative (I := I) (E := E)
      (u := e.baseSet) e.open_baseSet
  simpa [e, b] using
    (contMDiffOn_leviCivitaCorrection_section (I := I) (E := E) (cov := cov) e b
      e.open_baseSet (subset_refl _) hcov)

theorem contMDiffCovariantDerivative_leviCivitaConnection
    [T2Space M] [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 1] :
    ContMDiffCovariantDerivative (cov.leviCivitaConnection) 1 := by
  simpa [CovariantDerivative.leviCivitaConnection] using
    (ContMDiffCovariantDerivative.addOneForm (I := I) (E := E) (F := E) (V := TM) (n := 1)
      (cov := cov) (A := cov.leviCivitaCorrection)
      (contMDiff_leviCivitaCorrection_section (I := I) (E := E) (cov := cov)))

theorem leviCivitaConnection_isLeviCivita (cov : CovariantDerivative I E TM) :
    IsLeviCivita (leviCivitaConnection cov) := by
  exact ⟨cov.correctedConnection_isTorsionFree, cov.correctedConnection_isMetricCompatible⟩

end Existence

/-- The tangent bundle of a smooth finite-dimensional Riemannian manifold admits a `C^1`
Levi-Civita connection. -/
theorem leviCivitaConnection_contMDiff_nonempty
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I 2 E TM] :
    Nonempty { cov : CovariantDerivative I E TM //
      IsLeviCivita cov ∧ ContMDiffCovariantDerivative cov 1 } := by
  rcases exists_contMDiffAffineConnection (I := I) (E := E) (M := M) with ⟨cov, hcov⟩
  letI : ContMDiffCovariantDerivative cov 1 := hcov
  refine ⟨⟨leviCivitaConnection cov, ?_⟩⟩
  exact ⟨leviCivitaConnection_isLeviCivita cov,
    contMDiffCovariantDerivative_leviCivitaConnection (I := I) (E := E) (cov := cov)⟩

theorem exists_contMDiffLeviCivitaConnection
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I 2 E TM] :
    ∃ cov : CovariantDerivative I E TM,
      IsLeviCivita cov ∧ ContMDiffCovariantDerivative cov 1 := by
  rcases leviCivitaConnection_contMDiff_nonempty (I := I) (E := E) (M := M) with
    ⟨⟨cov, hcov, hcont⟩⟩
  exact ⟨cov, hcov, hcont⟩

noncomputable def someContMDiffLeviCivitaConnection
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I 2 E TM] :
    CovariantDerivative I E TM :=
  Classical.choose (exists_contMDiffLeviCivitaConnection (I := I) (E := E) (M := M))

theorem someContMDiffLeviCivitaConnection_isLeviCivita
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I 2 E TM] :
    IsLeviCivita (someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)) :=
  (Classical.choose_spec (exists_contMDiffLeviCivitaConnection (I := I) (E := E) (M := M))).1

theorem someContMDiffLeviCivitaConnection_contMDiff
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I 2 E TM] :
    ContMDiffCovariantDerivative
      (someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)) 1 :=
  (Classical.choose_spec (exists_contMDiffLeviCivitaConnection (I := I) (E := E) (M := M))).2

theorem leviCivitaConnection_nonempty [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    Nonempty { cov : CovariantDerivative I E TM // IsLeviCivita cov } := by
  rcases affineConnection_nonempty (I := I) (E := E) (M := M) with ⟨cov⟩
  exact ⟨⟨leviCivitaConnection cov, leviCivitaConnection_isLeviCivita cov⟩⟩

theorem exists_leviCivitaConnection [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    ∃ cov : CovariantDerivative I E TM, IsLeviCivita cov := by
  rcases leviCivitaConnection_nonempty (I := I) (E := E) (M := M) with ⟨⟨cov, hcov⟩⟩
  exact ⟨cov, hcov⟩

end CovariantDerivative
