/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Covariant derivatives along vector fields

This file packages the section-valued operation `σ ↦ ∇_X σ` for a bundled covariant derivative.
It also records a first batch of algebraic and regularity lemmas that will be used later in the
curvature development.
-/

@[expose] public noncomputable section

open Bundle Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [hField : NontriviallyNormedField 𝕜]
  {E : Type*} [hEGroup : NormedAddCommGroup E] [hESpace : NormedSpace 𝕜 E]
  {H : Type*} [hHTop : TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [hMTop : TopologicalSpace M] [hCharted : ChartedSpace H M]
  {F : Type*} [hFGroup : NormedAddCommGroup F] [hFSpace : NormedSpace 𝕜 F]
  {V : M → Type*} [hTotalTop : TopologicalSpace (TotalSpace F V)]
  [hVAdd : ∀ x, AddCommGroup (V x)] [hVModule : ∀ x, Module 𝕜 (V x)]
  [hVTop : ∀ x, TopologicalSpace (V x)] [hVAddTop : ∀ x, IsTopologicalAddGroup (V x)]
  [hVSMul : ∀ x, ContinuousSMul 𝕜 (V x)] [hFiber : FiberBundle F V]
  [hVector : VectorBundle 𝕜 F V]

namespace CovariantDerivative

variable (cov : CovariantDerivative I F V)

/-- The section `∇_X σ`. -/
def along (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  fun x ↦ cov σ x (X x)

@[simp]
lemma along_apply (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    cov.along X σ x = cov σ x (X x) :=
  rfl

@[simp]
lemma along_zero_left (σ : Π x : M, V x) :
    cov.along (0 : Π x : M, TangentSpace I x) σ = 0 := by
  funext x
  simp [CovariantDerivative.along]

@[simp]
lemma along_add_left (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    cov.along (X + Y) σ = cov.along X σ + cov.along Y σ := by
  funext x
  simp [CovariantDerivative.along, map_add]

@[simp]
lemma along_neg_left (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    cov.along (-X) σ = -cov.along X σ := by
  funext x
  simp [CovariantDerivative.along]

@[simp]
lemma along_sub_left (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    cov.along (X - Y) σ = cov.along X σ - cov.along Y σ := by
  funext x
  simp [sub_eq_add_neg]

lemma along_smul_left (f : M → 𝕜) (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    cov.along (f • X) σ = f • cov.along X σ := by
  funext x
  simp [CovariantDerivative.along]

variable {cov}

lemma along_add_right_apply {x : M}
    {X : Π x : M, TangentSpace I x} {σ σ' : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) :
    cov.along X (σ + σ') x = cov.along X σ x + cov.along X σ' x := by
  simp [CovariantDerivative.along, cov.isCovariantDerivativeOn.add hσ hσ']

lemma along_smul_right_apply {x : M}
    {f : M → 𝕜} {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x}
    (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) :
    cov.along X (f • σ) x = f x • cov.along X σ x + mvfderiv (I := I) f x (X x) • σ x := by
  simp [CovariantDerivative.along, cov.isCovariantDerivativeOn.leibniz hσ hf]

section Regularity

variable {n : WithTop ℕ∞}
  [IsManifold I 1 M]
  [ContMDiffVectorBundle n E (TangentSpace I : M → Type _ ) I]
  [ContMDiffVectorBundle n F V I]
  [ContMDiffCovariantDerivative cov n]
  {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x}

/-- If `∇` is a `C^n` covariant derivative, `X` is a `C^n` vector field, and `σ` is a
`C^(n+1)` section, then `∇_X σ` is a `C^n` section. -/
lemma contMDiff_along
    (hX : ContMDiff I (I.prod 𝓘(𝕜, E)) n (fun x ↦ TotalSpace.mk' E x (X x)))
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, F)) (n + 1) (fun x ↦ TotalSpace.mk' F x (σ x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (cov.along X σ x)) := by
  let Hcov : ContMDiffCovariantDerivativeOn F n cov.toFun univ :=
    (inferInstance : ContMDiffCovariantDerivative cov n).contMDiff
  have hCovSection :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] F)) n
        (fun m ↦
          TotalSpace.mk' (E →L[𝕜] F)
            (E := fun x : M ↦ TangentSpace I x →L[𝕜] V x) m (cov σ m))
        univ :=
    Hcov.contMDiff (by simpa [contMDiffOn_univ] using hσ)
  have hX' :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) n
        (fun x ↦ TotalSpace.mk' E x (X x)) univ := by
    simpa [contMDiffOn_univ] using hX
  simpa [CovariantDerivative.along, contMDiffOn_univ]
    using hCovSection.clm_bundle_apply hX'

/-- Adding a smooth bundle-valued one-form to a `C^n` covariant derivative preserves the
`C^n` regularity class. -/
lemma _root_.ContMDiffCovariantDerivativeOn.addOneForm
    {cov : CovariantDerivative I F V} {u : Set M}
    {A : ∀ x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x}
    (hcov : ContMDiffCovariantDerivativeOn F n cov.toFun u)
    (hA : ContMDiffOn I (I.prod 𝓘(𝕜, F →L[𝕜] E →L[𝕜] F)) n
      (fun x ↦
        TotalSpace.mk' (F →L[𝕜] E →L[𝕜] F)
          (E := fun x : M ↦ V x →L[𝕜] TangentSpace I x →L[𝕜] V x) x (A x)) u) :
    ContMDiffCovariantDerivativeOn F n (CovariantDerivative.addOneForm cov A).toFun u where
  contMDiff {σ} hσ := by
    have hCovSection :
        ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] F)) n
          (fun x ↦
            TotalSpace.mk' (E →L[𝕜] F)
              (E := fun x : M ↦ TangentSpace I x →L[𝕜] V x) x (cov σ x)) u :=
      hcov.contMDiff hσ
    have hσ' :
        ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (σ x)) u :=
      hσ.of_le <| le_add_of_nonneg_right (by simp)
    have hASection :
        ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] F)) n
          (fun x ↦
            TotalSpace.mk' (E →L[𝕜] F)
              (E := fun x : M ↦ TangentSpace I x →L[𝕜] V x) x (A x (σ x))) u :=
      hA.clm_bundle_apply hσ'
    simpa [CovariantDerivative.addOneForm] using hCovSection.add_section hASection

/-- Global version of `ContMDiffCovariantDerivativeOn.addOneForm`. -/
lemma _root_.ContMDiffCovariantDerivative.addOneForm
    {cov : CovariantDerivative I F V}
    [hcov : ContMDiffCovariantDerivative cov n]
    {A : ∀ x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x}
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] E →L[𝕜] F)) n
      (fun x ↦
        TotalSpace.mk' (F →L[𝕜] E →L[𝕜] F)
          (E := fun x : M ↦ V x →L[𝕜] TangentSpace I x →L[𝕜] V x) x (A x))) :
    ContMDiffCovariantDerivative (CovariantDerivative.addOneForm cov A) n where
  contMDiff := by
    exact hcov.contMDiff.addOneForm (by simpa [contMDiffOn_univ] using hA)

end Regularity
end CovariantDerivative
