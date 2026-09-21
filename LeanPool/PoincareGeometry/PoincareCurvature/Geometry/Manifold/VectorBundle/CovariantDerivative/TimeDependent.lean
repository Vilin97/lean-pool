/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
/-!
# Time-dependent geometric structures

This file packages roadmap point 3 as actual Lean formalization:
one-parameter families of sections, covariant derivatives, and smooth
Riemannian metrics, together with slicewise Levi-Civita constructions and
pointwise-in-time lifts of the static curvature operations.

The time variable is still treated explicitly as an `ℝ`-indexed family rather
than through a heavy time-differentiability theory. Spatial regularity is
tracked slice by slice, which is enough to talk coherently about the geometric
objects at time `t` that later Ricci-flow developments use.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- A one-parameter family of objects of type `α`. -/
abbrev TimeFamily (α : Type*) := ℝ → α

/-- A one-parameter family of sections of `V`. -/
abbrev TimeDependentSection (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] :=
  TimeFamily (Π x : M, V x)

/-- A one-parameter family of tangent vector fields. -/
abbrev TimeDependentVectorField := TimeFamily (Π x : M, TangentSpace I x)

/-- A one-parameter family of covariant derivatives on `V`. -/
abbrev TimeDependentCovariantDerivative :=
  TimeFamily (CovariantDerivative I F V)

namespace TimeFamily

variable {α : Type*}

/-- The constant time family at a fixed value. -/
def const (a : α) : TimeFamily α := fun _ => a

@[simp] lemma const_apply (a : α) (t : ℝ) : TimeFamily.const a t = a := rfl

@[ext] lemma ext {f g : TimeFamily α} (h : ∀ t, f t = g t) : f = g :=
  funext h

end TimeFamily

namespace TimeDependentSection

variable (σ : TimeDependentSection (𝕜 := 𝕜) (F := F) (V := V))

/-- Evaluate a time-dependent section at a fixed time. -/
def eval (t : ℝ) : Π x : M, V x := σ t

@[simp] lemma eval_apply (t : ℝ) (x : M) : σ.eval t x = σ t x := rfl

/-- The constant family determined by a single section. -/
def const (σ₀ : Π x : M, V x) : TimeDependentSection (𝕜 := 𝕜) (F := F) (V := V) :=
  TimeFamily.const σ₀

@[simp] lemma const_apply (σ₀ : Π x : M, V x) (t : ℝ) (x : M) :
    TimeDependentSection.const (𝕜 := 𝕜) (F := F) (V := V) σ₀ t x = σ₀ x := rfl

section Regularity

variable {n : WithTop ℕ∞} [IsManifold I 1 M] [ContMDiffVectorBundle n F V I]

/-- A time-dependent section is smooth in space if each time slice is smooth as a section on `M`. -/
def ContMDiffInSpace (n : WithTop ℕ∞)
    (σ : TimeDependentSection (𝕜 := 𝕜) (F := F) (V := V)) : Prop :=
  ∀ t : ℝ, ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (σ t x))

lemma contMDiffInSpace_const
    {σ₀ : Π x : M, V x}
    (hσ₀ : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (σ₀ x))) :
    ContMDiffInSpace (I := I) (F := F) (V := V) n
      (TimeDependentSection.const (𝕜 := 𝕜) (F := F) (V := V) σ₀) := by
  intro t
  simpa using hσ₀

end Regularity
end TimeDependentSection

namespace TimeDependentCovariantDerivative

variable (cov : TimeDependentCovariantDerivative (𝕜 := 𝕜) (I := I) (F := F) (V := V))

/-- Evaluate a time-dependent covariant derivative at a fixed time. -/
def eval (t : ℝ) : CovariantDerivative I F V := cov t

@[simp] lemma eval_apply (t : ℝ) : cov.eval t = cov t := rfl

/-- The constant family determined by a single covariant derivative. -/
def const (cov₀ : CovariantDerivative I F V) :
    TimeDependentCovariantDerivative (𝕜 := 𝕜) (I := I) (F := F) (V := V) :=
  TimeFamily.const cov₀

@[simp] lemma const_apply (cov₀ : CovariantDerivative I F V) (t : ℝ) :
    TimeDependentCovariantDerivative.const (𝕜 := 𝕜) (I := I) (F := F) (V := V) cov₀ t = cov₀ :=
  rfl

/-- The time-dependent section `t ↦ ∇(t)_{X(t)} σ(t)`. -/
def along
    (X : TimeDependentVectorField (𝕜 := 𝕜) (I := I) (M := M))
    (σ : TimeDependentSection (𝕜 := 𝕜) (F := F) (V := V)) :
    TimeDependentSection (𝕜 := 𝕜) (F := F) (V := V) :=
  fun t x ↦ (cov t).along (X t) (σ t) x

@[simp] lemma along_apply
    (X : TimeDependentVectorField (𝕜 := 𝕜) (I := I) (M := M))
    (σ : TimeDependentSection (𝕜 := 𝕜) (F := F) (V := V))
    (t : ℝ) (x : M) :
    cov.along X σ t x = (cov t).along (X t) (σ t) x := rfl

section Regularity

variable {n : WithTop ℕ∞} [IsManifold I 1 M]
  [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle n F V I]
  {cov : TimeDependentCovariantDerivative (𝕜 := 𝕜) (I := I) (F := F) (V := V)}
  {X : TimeDependentVectorField (𝕜 := 𝕜) (I := I) (M := M)}
  {σ : TimeDependentSection (𝕜 := 𝕜) (F := F) (V := V)}

/-- The `along` construction preserves smoothness in the manifold direction, slice by slice in time. -/
lemma contMDiffInSpace_along
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) n)
    (hX : TimeDependentSection.ContMDiffInSpace
      (I := I) (F := E) (V := (TangentSpace I : M → Type _)) n X)
    (hσ : TimeDependentSection.ContMDiffInSpace (I := I) (F := F) (V := V) (n + 1) σ) :
    TimeDependentSection.ContMDiffInSpace (I := I) (F := F) (V := V) n (cov.along X σ) := by
  intro t
  letI := hcov t
  exact (cov t).contMDiff_along (hX t) (hσ t)

end Regularity

end TimeDependentCovariantDerivative

section TangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

namespace TimeDependentCovariantDerivative

/-- The time-dependent raw curvature commutator obtained by slicing in time. -/
def curvatureAux
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (X Y Z : TimeDependentVectorField (𝕜 := ℝ) (I := I) (M := M)) :
    TimeDependentVectorField (𝕜 := ℝ) (I := I) (M := M) :=
  fun t x ↦ (cov t).curvatureAux (X t) (Y t) (Z t) x

@[simp] lemma curvatureAux_apply
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (X Y Z : TimeDependentVectorField (𝕜 := ℝ) (I := I) (M := M))
    (t : ℝ) (x : M) :
    curvatureAux (I := I) (M := M) cov X Y Z t x =
      (cov t).curvatureAux (X t) (Y t) (Z t) x := rfl

section Tensorial

/-- The bundled curvature tensor of a time slice. -/
def curvatureTensor
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v w : TM x) : TM x :=
  by
    letI := hcov t
    exact (cov t).curvatureTensor x u v w

@[simp] lemma curvatureTensor_apply
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v w : TM x) :
    curvatureTensor (I := I) (M := M) cov hcov t x u v w = (by
      letI := hcov t
      exact (cov t).curvatureTensor x u v w) := rfl

/-- The Ricci curvature of a time slice. -/
def ricciCurvature
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u w : TM x) : ℝ :=
  by
    letI := hcov t
    exact CovariantDerivative.ricciCurvature (cov := cov t) x u w

@[simp] lemma ricciCurvature_apply
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u w : TM x) :
    ricciCurvature (I := I) (M := M) cov hcov t x u w = (by
      letI := hcov t
      exact CovariantDerivative.ricciCurvature (cov := cov t) x u w) := rfl

/-- The scalar curvature of a time slice. -/
def scalarCurvature
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) : ℝ :=
  by
    letI := hcov t
    exact CovariantDerivative.scalarCurvature (cov := cov t) x

@[simp] lemma scalarCurvature_apply
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) :
    scalarCurvature (I := I) (M := M) cov hcov t x = (by
      letI := hcov t
      exact CovariantDerivative.scalarCurvature (cov := cov t) x) := rfl

/-- The sectional-curvature numerator of a time slice. -/
def sectionalCurvatureNumerator
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) : ℝ :=
  by
    letI := hcov t
    exact CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x u v

@[simp] lemma sectionalCurvatureNumerator_apply
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    sectionalCurvatureNumerator (I := I) (M := M) cov hcov t x u v = (by
      letI := hcov t
      exact CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x u v) := rfl

/-- The sectional-curvature denominator of a time slice. -/
def sectionalCurvatureDenominator
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) : ℝ :=
  CovariantDerivative.sectionalCurvatureDenominator (I := I) x u v

@[simp] lemma sectionalCurvatureDenominator_apply
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    sectionalCurvatureDenominator (I := I) (M := M) cov hcov t x u v = (by
      exact CovariantDerivative.sectionalCurvatureDenominator (I := I) x u v) := rfl

/-- The sectional curvature of a time slice. -/
def sectionalCurvature
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x)
    (h : sectionalCurvatureDenominator
      (I := I) (M := M) cov hcov t x u v ≠ 0) : ℝ :=
  by
    letI := hcov t
    exact CovariantDerivative.sectionalCurvature (cov := cov t) x u v
      (show CovariantDerivative.sectionalCurvatureDenominator (I := I) x u v ≠ 0 from h)

@[simp] lemma sectionalCurvature_apply
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x)
    (h : sectionalCurvatureDenominator
      (I := I) (M := M) cov hcov t x u v ≠ 0) :
    sectionalCurvature (I := I) (M := M) cov hcov t x u v h = (by
      letI := hcov t
      exact CovariantDerivative.sectionalCurvature (cov := cov t) x u v
        (show CovariantDerivative.sectionalCurvatureDenominator (I := I) x u v ≠ 0 from h)) := rfl

end Tensorial
end TimeDependentCovariantDerivative
end TangentBundle

section TimeDependentMetrics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- A one-parameter family of `C^2` Riemannian metrics on the tangent bundle. -/
abbrev TimeDependentRiemannianMetric :=
  TimeFamily (Bundle.ContMDiffRiemannianMetric I 2 E TM)

namespace TimeDependentRiemannianMetric

variable (g : TimeDependentRiemannianMetric (I := I) (M := M))

/-- Evaluate a time-dependent Riemannian metric at a fixed time. -/
def eval (t : ℝ) : Bundle.ContMDiffRiemannianMetric I 2 E TM := g t

@[simp] lemma eval_apply (t : ℝ) : g.eval t = g t := rfl

/-- The constant family determined by a single smooth Riemannian metric. -/
def const (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) :
    TimeDependentRiemannianMetric (I := I) (M := M) :=
  TimeFamily.const g₀

@[simp] lemma const_apply (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) (t : ℝ) :
    TimeDependentRiemannianMetric.const (I := I) (M := M) g₀ t = g₀ := rfl

/-- The smoothness package carried by a fixed time slice of a time-dependent metric. -/
lemma slice_isContMDiffRiemannianBundle (t : ℝ) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    IsContMDiffRiemannianBundle I 1 E TM := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  infer_instance

/-- The fibrewise inner product determined by a time-dependent metric at time `t`. -/
def inner (t : ℝ) (x : M) (u v : TM x) : ℝ :=
  (g t).inner x u v

@[simp] lemma inner_apply (t : ℝ) (x : M) (u v : TM x) :
    inner (I := I) (M := M) g t x u v = (g t).inner x u v := rfl

/-- A time-dependent connection family is metric-compatible with `g` if each time slice is. -/
def IsMetricCompatible
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)) :
    Prop :=
  ∀ t : ℝ,
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    (cov t).IsMetricCompatibleTangent

/-- A time-dependent connection family is Levi-Civita for `g` if each time slice is. -/
def IsLeviCivita
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)) :
    Prop :=
  ∀ t : ℝ,
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    (cov t).IsLeviCivita

/-- On zero-dimensional tangent fibers, every time-dependent affine connection is Levi-Civita for
every time-dependent Riemannian metric. -/
theorem isLeviCivita_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)) :
    g.IsLeviCivita cov := by
  intro t
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle t
  exact CovariantDerivative.isLeviCivita_of_subsingleton_tangent (I := I) (E := E) (M := M)
    (cov t)

/-- The time-dependent Levi-Civita correction applied slice by slice to a family of affine connections. -/
noncomputable def leviCivitaConnection
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)) :
    TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) :=
  fun t ↦ by
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle t
    exact CovariantDerivative.leviCivitaConnection (I := I) (E := E) (M := M) (cov t)

theorem leviCivitaConnection_isLeviCivita
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)) :
    g.IsLeviCivita (g.leviCivitaConnection cov) := by
  intro t
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle t
  exact CovariantDerivative.leviCivitaConnection_isLeviCivita (I := I) (E := E) (M := M) (cov t)

theorem contMDiffCovariantDerivative_leviCivitaConnection
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1) :
    ∀ t : ℝ, ContMDiffCovariantDerivative (g.leviCivitaConnection cov t) 1 := by
  intro t
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact CovariantDerivative.contMDiffCovariantDerivative_leviCivitaConnection
    (I := I) (E := E) (M := M) (cov := cov t)

/-- Two time-dependent Levi-Civita families for the same metric agree at every time slice. -/
theorem eq_of_isLeviCivita
    {cov cov' : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)}
    (hcov : g.IsLeviCivita cov) (hcov' : g.IsLeviCivita cov')
    {t : ℝ} {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    cov t σ x = cov' t σ x := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact
    CovariantDerivative.eq_of_isLeviCivita
      (I := I) (E := E) (M := M) (cov := cov t) (cov' := cov' t) (hcov t) (hcov' t) hσ

/-- The slicewise Levi-Civita family constructed from any background family is the unique
time-dependent Levi-Civita family for `g`. -/
theorem leviCivitaConnection_eq_of_isLeviCivita
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    {cov' : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)}
    (hcov' : g.IsLeviCivita cov')
    {t : ℝ} {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    g.leviCivitaConnection cov t σ x = cov' t σ x := by
  exact g.eq_of_isLeviCivita (cov := g.leviCivitaConnection cov) (cov' := cov')
    (g.leviCivitaConnection_isLeviCivita cov) hcov' hσ

/-- The slicewise Levi-Civita correction is independent of the chosen background family. -/
theorem leviCivitaConnection_eq_leviCivitaConnection
    (cov cov' : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    {t : ℝ} {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    g.leviCivitaConnection cov t σ x = g.leviCivitaConnection cov' t σ x := by
  exact g.eq_of_isLeviCivita
    (cov := g.leviCivitaConnection cov)
    (cov' := g.leviCivitaConnection cov')
    (g.leviCivitaConnection_isLeviCivita cov)
    (g.leviCivitaConnection_isLeviCivita cov') hσ

/-- Ricci curvature of a time slice, evaluated using the metric carried by `g t`. -/
def ricciCurvature
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u w : TM x) : ℝ := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact CovariantDerivative.ricciCurvature (cov := cov t) x u w

@[simp] lemma ricciCurvature_apply
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u w : TM x) :
    g.ricciCurvature cov hcov t x u w = (by
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact CovariantDerivative.ricciCurvature (cov := cov t) x u w) := rfl

/-- Time-dependent Ricci symmetry from first Bianchi and curvature pair symmetry at each time
slice. -/
theorem ricciCurvature_symm_of_curvature_inner_pair_symm_of_firstBianchi
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (hBianchi : ∀ (t : ℝ) (x : M) (a b c : TM x),
      curvatureTensor (cov := cov t) x a b c +
          curvatureTensor (cov := cov t) x b c a +
          curvatureTensor (cov := cov t) x c a b = 0)
    (hpair : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      ∀ (a b c d : TM x),
        Inner.inner ℝ (curvatureTensor (cov := cov t) x a b c) d =
          Inner.inner ℝ (curvatureTensor (cov := cov t) x c d a) b)
    (t : ℝ) (x : M) (u w : TM x) :
    g.ricciCurvature cov hcov t x u w = g.ricciCurvature cov hcov t x w u := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  haveI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact CovariantDerivative.ricciCurvature_symm_of_curvature_inner_pair_symm_of_firstBianchi
    (cov := cov t) (hBianchi t) (hpair t) x u w

/-- Time-dependent Ricci symmetry from torsion-freeness and curvature pair symmetry at each time
slice. -/
theorem ricciCurvature_symm_of_curvature_inner_pair_symm_of_torsion_eq_zero
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (hT : ∀ t : ℝ, (cov t).torsion = 0)
    (hpair : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      ∀ (a b c d : TM x),
        Inner.inner ℝ (curvatureTensor (cov := cov t) x a b c) d =
          Inner.inner ℝ (curvatureTensor (cov := cov t) x c d a) b)
    (t : ℝ) (x : M) (u w : TM x) :
    g.ricciCurvature cov hcov t x u w = g.ricciCurvature cov hcov t x w u := by
  exact _root_.CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature_symm_of_curvature_inner_pair_symm_of_firstBianchi
    (g := g) cov hcov
    (fun t x a b c =>
      firstBianchi_curvatureTensor_of_torsion_eq_zero (cov := cov t) (hT t) x a b c)
    hpair t x u w

/-- Time-dependent Ricci symmetry from first Bianchi and skew-adjointness of each curvature
operator at each time slice. -/
theorem ricciCurvature_symm_of_curvature_inner_skew_adjoint_of_firstBianchi
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (hBianchi : ∀ (t : ℝ) (x : M) (a b c : TM x),
      curvatureTensor (cov := cov t) x a b c +
          curvatureTensor (cov := cov t) x b c a +
          curvatureTensor (cov := cov t) x c a b = 0)
    (hskew : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      ∀ (a b c d : TM x),
        Inner.inner ℝ (curvatureTensor (cov := cov t) x a b c) d +
          Inner.inner ℝ c (curvatureTensor (cov := cov t) x a b d) = 0)
    (t : ℝ) (x : M) (u w : TM x) :
    g.ricciCurvature cov hcov t x u w = g.ricciCurvature cov hcov t x w u := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  haveI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact CovariantDerivative.ricciCurvature_symm_of_curvature_inner_skew_adjoint_of_firstBianchi
    (cov := cov t) (hBianchi t) (hskew t) x u w

/-- Time-dependent Ricci symmetry from torsion-freeness and skew-adjointness of each curvature
operator at each time slice. -/
theorem ricciCurvature_symm_of_curvature_inner_skew_adjoint_of_torsion_eq_zero
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (hT : ∀ t : ℝ, (cov t).torsion = 0)
    (hskew : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      ∀ (a b c d : TM x),
        Inner.inner ℝ (curvatureTensor (cov := cov t) x a b c) d +
          Inner.inner ℝ c (curvatureTensor (cov := cov t) x a b d) = 0)
    (t : ℝ) (x : M) (u w : TM x) :
    g.ricciCurvature cov hcov t x u w = g.ricciCurvature cov hcov t x w u := by
  exact _root_.CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature_symm_of_curvature_inner_skew_adjoint_of_firstBianchi
    (g := g) cov hcov
    (fun t x a b c =>
      firstBianchi_curvatureTensor_of_torsion_eq_zero (cov := cov t) (hT t) x a b c)
    hskew t x u w

/-- Time-dependent Ricci symmetry from torsion-freeness and metric compatibility at each time
slice. -/
theorem ricciCurvature_symm_of_metricCompatible_of_torsion_eq_zero
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (hT : ∀ t : ℝ, (cov t).torsion = 0)
    (hmetric : g.IsMetricCompatible cov)
    (t : ℝ) (x : M) (u w : TM x) :
    g.ricciCurvature cov hcov t x u w = g.ricciCurvature cov hcov t x w u := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact CovariantDerivative.ricciCurvature_symm_of_metricCompatibleTangent_of_torsion_eq_zero
    (cov := cov t) (hT t) (hmetric t) x u w

/-- Time-dependent Ricci symmetry for Levi-Civita connection families. -/
theorem ricciCurvature_symm_of_isLeviCivita
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (t : ℝ) (x : M) (u w : TM x) :
    g.ricciCurvature cov hcov t x u w = g.ricciCurvature cov hcov t x w u := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact CovariantDerivative.ricciCurvature_symm_of_isLeviCivita
    (cov := cov t) (hLevi t) x u w

/-- Ricci curvature of a time-dependent metric family is independent of the chosen Levi-Civita
family used to compute it. -/
theorem ricciCurvature_eq_of_isLeviCivita
    {cov cov' : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)}
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (hcov' : ∀ t : ℝ, ContMDiffCovariantDerivative (cov' t) 1)
    (hLevi : g.IsLeviCivita cov) (hLevi' : g.IsLeviCivita cov')
    (t : ℝ) (x : M) (u w : TM x) :
    g.ricciCurvature cov hcov t x u w = g.ricciCurvature cov' hcov' t x u w := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle t
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ContMDiffCovariantDerivative (cov' t) 1 := hcov' t
  exact CovariantDerivative.ricciCurvature_eq_of_isLeviCivita
    (I := I) (M := M) (cov := cov t) (cov' := cov' t) (hLevi t) (hLevi' t) x u w

/-- Scalar curvature of a time slice, evaluated using the metric carried by `g t`. -/
def scalarCurvature
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) : ℝ := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact CovariantDerivative.scalarCurvature (cov := cov t) x

@[simp] lemma scalarCurvature_apply
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) :
    g.scalarCurvature cov hcov t x = (by
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact CovariantDerivative.scalarCurvature (cov := cov t) x) := rfl

/-- Scalar curvature of a time-dependent metric family is independent of the chosen Levi-Civita
family used to compute it. -/
theorem scalarCurvature_eq_of_isLeviCivita
    {cov cov' : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)}
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (hcov' : ∀ t : ℝ, ContMDiffCovariantDerivative (cov' t) 1)
    (hLevi : g.IsLeviCivita cov) (hLevi' : g.IsLeviCivita cov')
    (t : ℝ) (x : M) :
    g.scalarCurvature cov hcov t x = g.scalarCurvature cov' hcov' t x := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle t
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ContMDiffCovariantDerivative (cov' t) 1 := hcov' t
  exact CovariantDerivative.scalarCurvature_eq_of_isLeviCivita
    (I := I) (M := M) (cov := cov t) (cov' := cov' t) (hLevi t) (hLevi' t) x

/-- The sectional-curvature numerator of a time slice, evaluated using the metric carried by `g t`. -/
def sectionalCurvatureNumerator
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) : ℝ := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x u v

@[simp] lemma sectionalCurvatureNumerator_apply
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    g.sectionalCurvatureNumerator cov hcov t x u v = (by
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact CovariantDerivative.sectionalCurvatureNumerator (cov := cov t) x u v) := rfl

/-- The Gram determinant associated to the time-dependent metric slice `g t`. -/
def sectionalCurvatureDenominator (t : ℝ) (x : M) (u v : TM x) : ℝ := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact CovariantDerivative.sectionalCurvatureDenominator (I := I) x u v

@[simp] lemma sectionalCurvatureDenominator_apply (t : ℝ) (x : M) (u v : TM x) :
    g.sectionalCurvatureDenominator t x u v = (by
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact CovariantDerivative.sectionalCurvatureDenominator (I := I) x u v) := rfl

/-- The sectional curvature associated to a time slice and a nondegenerate plane. -/
def sectionalCurvature
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x)
    (h : g.sectionalCurvatureDenominator t x u v ≠ 0) : ℝ := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact CovariantDerivative.sectionalCurvature (cov := cov t) x u v
    (show CovariantDerivative.sectionalCurvatureDenominator (I := I) x u v ≠ 0 from h)

@[simp] lemma sectionalCurvature_apply
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x)
    (h : g.sectionalCurvatureDenominator t x u v ≠ 0) :
    g.sectionalCurvature cov hcov t x u v h = (by
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact CovariantDerivative.sectionalCurvature (cov := cov t) x u v
        (show CovariantDerivative.sectionalCurvatureDenominator (I := I) x u v ≠ 0 from h)) := rfl

section Existence

variable [SigmaCompactSpace M]

/-- A time-dependent smooth metric admits a slicewise Levi-Civita family. -/
theorem leviCivitaConnection_contMDiff_nonempty :
    Nonempty
      { cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) //
        g.IsLeviCivita cov ∧ ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1 } := by
  letI : Bundle.RiemannianBundle TM := ⟨(g 0).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  rcases CovariantDerivative.exists_contMDiffAffineConnection (I := I) (E := E) (M := M) with
    ⟨cov₀, hcov₀⟩
  let cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) :=
    fun _ ↦ cov₀
  have hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1 := fun _ ↦ hcov₀
  refine ⟨⟨g.leviCivitaConnection cov, ?_⟩⟩
  exact ⟨g.leviCivitaConnection_isLeviCivita cov,
    g.contMDiffCovariantDerivative_leviCivitaConnection cov hcov⟩

theorem exists_contMDiffLeviCivitaConnection :
    ∃ cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM),
      g.IsLeviCivita cov ∧ ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1 := by
  rcases g.leviCivitaConnection_contMDiff_nonempty (I := I) (M := M) with ⟨⟨cov, hcov, hcont⟩⟩
  exact ⟨cov, hcov, hcont⟩

noncomputable def someContMDiffLeviCivitaConnection :
    TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) :=
  Classical.choose (g.exists_contMDiffLeviCivitaConnection (I := I) (M := M))

theorem someContMDiffLeviCivitaConnection_isLeviCivita :
    g.IsLeviCivita (g.someContMDiffLeviCivitaConnection (I := I) (M := M)) :=
  (Classical.choose_spec (g.exists_contMDiffLeviCivitaConnection (I := I) (M := M))).1

theorem someContMDiffLeviCivitaConnection_contMDiff :
    ∀ t : ℝ,
      ContMDiffCovariantDerivative
        ((g.someContMDiffLeviCivitaConnection (I := I) (M := M)) t) 1 :=
  (Classical.choose_spec (g.exists_contMDiffLeviCivitaConnection (I := I) (M := M))).2

/-- Any slicewise Levi-Civita family for a `C²` time-dependent Riemannian metric is slicewise
`C¹`, because it agrees with the chosen smooth Levi-Civita family on smooth sections. -/
theorem contMDiffCovariantDerivative_of_isLeviCivita
    {cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)}
    (hcov : g.IsLeviCivita cov) :
    ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1 := by
  intro t
  let cov₀ := g.someContMDiffLeviCivitaConnection (I := I) (M := M)
  have hcov₀ : g.IsLeviCivita cov₀ :=
    g.someContMDiffLeviCivitaConnection_isLeviCivita (I := I) (M := M)
  have hcont₀ : ContMDiffCovariantDerivative (cov₀ t) 1 :=
    g.someContMDiffLeviCivitaConnection_contMDiff (I := I) (M := M) t
  refine ⟨?_⟩
  refine ⟨?_⟩
  intro σ hσ
  exact (hcont₀.contMDiff.contMDiff hσ).congr (by
    intro x hx
    have hσat :
        ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 + 1) (T% σ) x := by
      exact contMDiffWithinAt_univ.mp (hσ x hx)
    have hσx : MDiffAt (T% σ) x := hσat.mdifferentiableAt (by simp)
    simp [cov₀, g.eq_of_isLeviCivita hcov hcov₀ hσx])

theorem leviCivitaConnection_nonempty :
    Nonempty
      { cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) //
        g.IsLeviCivita cov } := by
  rcases g.leviCivitaConnection_contMDiff_nonempty (I := I) (M := M) with
    ⟨⟨cov, hcov, _⟩⟩
  exact ⟨⟨cov, hcov⟩⟩

/-- A time-dependent smooth metric admits a slicewise Levi-Civita connection family. -/
theorem exists_leviCivitaConnection :
    ∃ cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM),
      g.IsLeviCivita cov := by
  rcases g.exists_contMDiffLeviCivitaConnection (I := I) (M := M) with ⟨cov, hcov, _⟩
  exact ⟨cov, hcov⟩

end Existence

end TimeDependentRiemannianMetric

end TimeDependentMetrics

end CovariantDerivative
