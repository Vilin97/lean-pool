/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.InducedHom
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.HomEvaluation

/-!
# Curvature of an induced hom-bundle connection

This file records the curvature product rule for an induced connection on a
hom bundle.  The statement is deliberately pointwise and keeps the
differentiability hypotheses explicit: it is the static geometric bridge
used later when a time-dependent curvature calculation is reduced to
covariant derivatives of tensor fields.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ V₂ : M → Type*}
  [TopologicalSpace (TotalSpace F₁ V₁)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [∀ x, FiniteDimensional ℝ (V₁ x)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [∀ x, FiniteDimensional ℝ (V₂ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle 2 F₁ V₁ I] [ContMDiffVectorBundle 2 F₂ V₂ I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "Hom₁₂" => (fun x : M => V₁ x →L[ℝ] V₂ x)

variable (cov₁ : CovariantDerivative I F₁ V₁)
  (cov₂ : CovariantDerivative I F₂ V₂)

theorem curvatureAux_inducedHom_apply
    {φ : ∀ x : M, Hom₁₂ x} {σ : ∀ x : M, V₁ x}
    {X Y : ∀ x : M, TM x} {x : M}
    (hφ : ∀ y, MDiffAt
      (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) z (φ z)) y)
    (hσ : ∀ y, MDiffAt (T% σ) y)
    (hφX : ∀ y, MDiffAt
      (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) z
        (inducedHomCovariantDerivative cov₁ cov₂ φ z (X z))) y)
    (hφY : ∀ y, MDiffAt
      (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) z
        (inducedHomCovariantDerivative cov₁ cov₂ φ z (Y z))) y)
    (hQXσ : ∀ y, MDiffAt (T% (cov₁.along X σ)) y)
    (hQYσ : ∀ y, MDiffAt (T% (cov₁.along Y σ)) y)
    (hP_Yφσ : MDiffAt (T% (cov₂.along Y (fun z => φ z (σ z)))) x)
    (hP_Xφσ : MDiffAt (T% (cov₂.along X (fun z => φ z (σ z)))) x)
    (hφQX : MDiffAt (fun z => TotalSpace.mk' F₂ z
      (φ z (cov₁.along X σ z))) x)
    (hφQY : MDiffAt (fun z => TotalSpace.mk' F₂ z
      (φ z (cov₁.along Y σ z))) x) :
    (inducedHomCovariantDerivative cov₁ cov₂).curvatureAux X Y φ x (σ x) =
      cov₂.curvatureAux X Y (fun y => φ y (σ y)) x -
        φ x (cov₁.curvatureAux X Y σ x) := by
  let D := inducedHomCovariantDerivative cov₁ cov₂
  let B := VectorField.mlieBracket I X Y
  have hsub {σ τ : ∀ y : M, V₂ y} {W : ∀ y : M, TM y}
      {z : M} (hσ : MDiffAt (T% σ) z) (hτ : MDiffAt (T% τ) z) :
      cov₂.along W (σ - τ) z =
        cov₂.along W σ z - cov₂.along W τ z := by
    have hneg : MDiffAt (T% (-τ)) z := mdifferentiableAt_neg_section hτ
    have hsum := cov₂.along_add_right_apply (x := z) (X := W) hσ hneg
    have hneg' : cov₂.along W (-τ) z = -cov₂.along W τ z := by
      have h := cov₂.along_smul_right_apply (x := z) (f := fun _ : M => (-1 : ℝ))
        (X := W) (σ := τ) mdifferentiableAt_const hτ
      have hscalar : (fun _ : M => (-1 : ℝ)) • τ = -τ := by
        funext y
        simp
      rw [hscalar] at h
      simpa [mvfderiv] using h
    rw [sub_eq_add_neg, hsum, hneg']
    abel
  have hprod (A : ∀ y : M, Hom₁₂ y) (τ : ∀ y : M, V₁ y)
      (W : ∀ y : M, TM y)
      (hA : ∀ y, MDiffAt
        (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) z (A z)) y)
      (hτ : ∀ y, MDiffAt (T% τ) y) :
      (fun y => (D A y (W y)) (τ y)) =
        (fun y => cov₂.along W (fun z => A z (τ z)) y -
          A y (cov₁.along W τ y)) := by
    funext y
    have h := inducedHomCovariantDerivative_apply_section_general
      cov₁ cov₂ (x := y) (u := W y) (hA y) (hτ y)
    simpa [D, CovariantDerivative.along] using h
  have hpY := hprod φ σ Y hφ hσ
  have hpX := hprod φ σ X hφ hσ
  have hpB := hprod φ σ B hφ hσ
  have hpYQX := hprod φ (cov₁.along X σ) Y hφ hQXσ
  have hpXQY := hprod φ (cov₁.along Y σ) X hφ hQYσ
  have h1 :
      (D (fun y => D φ y (Y y)) x (X x)) (σ x) =
        cov₂.along X
            (fun y => D φ y (Y y) (σ y)) x -
          (D φ x (Y x)) (cov₁.along X σ x) := by
    simpa [D, CovariantDerivative.along] using congrFun
      (hprod (fun y => D φ y (Y y)) σ X hφY hσ) x
  have h2 :
      (D (fun y => D φ y (X y)) x (Y x)) (σ x) =
        cov₂.along Y
            (fun y => D φ y (X y) (σ y)) x -
          (D φ x (X x)) (cov₁.along Y σ x) := by
    simpa [D, CovariantDerivative.along] using congrFun
      (hprod (fun y => D φ y (X y)) σ Y hφX hσ) x
  have h1n :
      (D (D.along Y φ) x (X x)) (σ x) =
        cov₂.along X
            (fun y => D φ y (Y y) (σ y)) x -
          (D φ x (Y x)) (cov₁.along X σ x) := by
    change (D (fun y => D φ y (Y y)) x (X x)) (σ x) = _
    exact h1
  have h2n :
      (D (D.along X φ) x (Y x)) (σ x) =
        cov₂.along Y
            (fun y => D φ y (X y) (σ y)) x -
          (D φ x (X x)) (cov₁.along Y σ x) := by
    change (D (fun y => D φ y (X y)) x (Y x)) (σ x) = _
    exact h2
  have h1' :
      (D (D.along Y φ) x (X x)) (σ x) =
        cov₂.along X (cov₂.along Y (fun z => φ z (σ z))) x -
          cov₂.along X (fun z => φ z (cov₁.along Y σ z)) x -
          (cov₂.along Y (fun z => φ z (cov₁.along X σ z)) x -
            φ x (cov₁.along Y (cov₁.along X σ) x)) := by
    rw [h1n, hpY, congrFun hpYQX x]
    have hsubY := hsub (W := X) (z := x) hP_Yφσ hφQY
    have hsubY' : cov₂.along X
        (fun y => cov₂.along Y (fun z => φ z (σ z)) y -
          φ y (cov₁.along Y σ y)) x =
        cov₂.along X (cov₂.along Y (fun z => φ z (σ z))) x -
          cov₂.along X (fun z => φ z (cov₁.along Y σ z)) x := by
      have hfunY :
          (fun y => cov₂.along Y (fun z => φ z (σ z)) y -
            φ y (cov₁.along Y σ y)) =
            cov₂.along Y (fun z => φ z (σ z)) -
              (fun y => φ y (cov₁.along Y σ y)) := by
        funext y
        rfl
      rw [hfunY]
      exact hsubY
    rw [hsubY']
  have h2' :
      (D (D.along X φ) x (Y x)) (σ x) =
        cov₂.along Y (cov₂.along X (fun z => φ z (σ z))) x -
          cov₂.along Y (fun z => φ z (cov₁.along X σ z)) x -
          (cov₂.along X (fun z => φ z (cov₁.along Y σ z)) x -
            φ x (cov₁.along X (cov₁.along Y σ) x)) := by
    rw [h2n, hpX, congrFun hpXQY x]
    have hsubX := hsub (W := Y) (z := x) hP_Xφσ hφQX
    have hsubX' : cov₂.along Y
        (fun y => cov₂.along X (fun z => φ z (σ z)) y -
          φ y (cov₁.along X σ y)) x =
        cov₂.along Y (cov₂.along X (fun z => φ z (σ z))) x -
          cov₂.along Y (fun z => φ z (cov₁.along X σ z)) x := by
      have hfunX :
          (fun y => cov₂.along X (fun z => φ z (σ z)) y -
            φ y (cov₁.along X σ y)) =
            cov₂.along X (fun z => φ z (σ z)) -
              (fun y => φ y (cov₁.along X σ y)) := by
        funext y
        rfl
      rw [hfunX]
      exact hsubX
    rw [hsubX']
  have h3 :
      D.along B φ x (σ x) =
        cov₂.along B (fun z => φ z (σ z)) x -
          φ x (cov₁.along B σ x) := by
    simpa [D, CovariantDerivative.along] using congrFun hpB x
  have hcurvD :
      D.curvatureAux X Y φ x (σ x) =
        (D (D.along Y φ) x (X x)) (σ x) -
          (D (D.along X φ) x (Y x)) (σ x) -
          (D.along B φ x) (σ x) := by
    simp only [CovariantDerivative.curvatureAux, CovariantDerivative.along,
      Pi.sub_apply, ContinuousLinearMap.sub_apply, B]
  rw [hcurvD, h1', h2', h3]
  simp [CovariantDerivative.curvatureAux, CovariantDerivative.along, B]
  simp only [map_sub, map_add, sub_eq_add_neg]
  abel

/-! A localized version of the induced-Hom curvature formula.  The original
sections are differentiable globally so their product-rule identity can be
differentiated once more; the derived sections need only be differentiable
where the curvature is evaluated. -/
theorem curvatureAux_inducedHom_apply_at
    {φ : ∀ x : M, Hom₁₂ x} {σ : ∀ x : M, V₁ x}
    {X Y : ∀ x : M, TM x} {x : M}
    (hφ : ∀ y, MDiffAt
      (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) z (φ z)) y)
    (hσ : ∀ y, MDiffAt (T% σ) y)
    (hφX : MDiffAt
      (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) z
        (inducedHomCovariantDerivative cov₁ cov₂ φ z (X z))) x)
    (hφY : MDiffAt
      (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) z
        (inducedHomCovariantDerivative cov₁ cov₂ φ z (Y z))) x)
    (hQXσ : MDiffAt (T% (cov₁.along X σ)) x)
    (hQYσ : MDiffAt (T% (cov₁.along Y σ)) x)
    (hP_Yφσ : MDiffAt
      (T% (cov₂.along Y (fun z => φ z (σ z)))) x)
    (hP_Xφσ : MDiffAt
      (T% (cov₂.along X (fun z => φ z (σ z)))) x)
    (hφQX : MDiffAt
      (fun z => TotalSpace.mk' F₂ z (φ z (cov₁.along X σ z))) x)
    (hφQY : MDiffAt
      (fun z => TotalSpace.mk' F₂ z (φ z (cov₁.along Y σ z))) x) :
    (inducedHomCovariantDerivative cov₁ cov₂).curvatureAux X Y φ x (σ x) =
      cov₂.curvatureAux X Y (fun y => φ y (σ y)) x -
        φ x (cov₁.curvatureAux X Y σ x) := by
  let D := inducedHomCovariantDerivative cov₁ cov₂
  let B := VectorField.mlieBracket I X Y
  have hsub {τ υ : ∀ y : M, V₂ y} {W : ∀ y : M, TM y}
      (hτ : MDiffAt (T% τ) x) (hυ : MDiffAt (T% υ) x) :
      cov₂.along W (τ - υ) x =
        cov₂.along W τ x - cov₂.along W υ x := by
    have hneg : MDiffAt (T% (-υ)) x := mdifferentiableAt_neg_section hυ
    have hsum := cov₂.along_add_right_apply (x := x) (X := W) hτ hneg
    have hneg' : cov₂.along W (-υ) x = -cov₂.along W υ x := by
      have h := cov₂.along_smul_right_apply (x := x)
        (f := fun _ : M => (-1 : ℝ)) (X := W) (σ := υ)
        mdifferentiableAt_const hυ
      have hscalar : (fun _ : M => (-1 : ℝ)) • υ = -υ := by
        funext y
        simp
      rw [hscalar] at h
      simpa [mvfderiv] using h
    rw [sub_eq_add_neg, hsum, hneg']
    abel
  have hprod (A : ∀ y : M, Hom₁₂ y) (τ : ∀ y : M, V₁ y)
      (W : ∀ y : M, TM y)
      (hA : ∀ y, MDiffAt
        (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) z (A z)) y)
      (hτ : ∀ y, MDiffAt (T% τ) y) :
      (fun y => (D A y (W y)) (τ y)) =
        (fun y => cov₂.along W (fun z => A z (τ z)) y -
          A y (cov₁.along W τ y)) := by
    funext y
    have h := inducedHomCovariantDerivative_apply_section_general
      cov₁ cov₂ (x := y) (u := W y) (hA y) (hτ y)
    simpa [D, CovariantDerivative.along] using h
  have hprodAt (A : ∀ y : M, Hom₁₂ y) (τ : ∀ y : M, V₁ y)
      (W : ∀ y : M, TM y)
      (hA : MDiffAt
        (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) z (A z)) x)
      (hτ : MDiffAt (T% τ) x) :
      (D A x (W x)) (τ x) =
        cov₂.along W (fun z => A z (τ z)) x -
          A x (cov₁.along W τ x) := by
    have h := inducedHomCovariantDerivative_apply_section_general
      cov₁ cov₂ (x := x) (u := W x) hA hτ
    simpa [D, CovariantDerivative.along] using h
  have hpY := hprod φ σ Y hφ hσ
  have hpX := hprod φ σ X hφ hσ
  have hpB := hprod φ σ B hφ hσ
  have hpYQX := hprodAt φ (cov₁.along X σ) Y (hφ x) hQXσ
  have hpXQY := hprodAt φ (cov₁.along Y σ) X (hφ x) hQYσ
  have h1 :
      (D (fun y => D φ y (Y y)) x (X x)) (σ x) =
        cov₂.along X
            (fun y => D φ y (Y y) (σ y)) x -
          (D φ x (Y x)) (cov₁.along X σ x) := by
    exact hprodAt (fun y => D φ y (Y y)) σ X hφY (hσ x)
  have h2 :
      (D (fun y => D φ y (X y)) x (Y x)) (σ x) =
        cov₂.along Y
            (fun y => D φ y (X y) (σ y)) x -
          (D φ x (X x)) (cov₁.along Y σ x) := by
    exact hprodAt (fun y => D φ y (X y)) σ Y hφX (hσ x)
  have h1n :
      (D (D.along Y φ) x (X x)) (σ x) =
        cov₂.along X
            (fun y => D φ y (Y y) (σ y)) x -
          (D φ x (Y x)) (cov₁.along X σ x) := by
    change (D (fun y => D φ y (Y y)) x (X x)) (σ x) = _
    exact h1
  have h2n :
      (D (D.along X φ) x (Y x)) (σ x) =
        cov₂.along Y
            (fun y => D φ y (X y) (σ y)) x -
          (D φ x (X x)) (cov₁.along Y σ x) := by
    change (D (fun y => D φ y (X y)) x (Y x)) (σ x) = _
    exact h2
  have h1' :
      (D (D.along Y φ) x (X x)) (σ x) =
        cov₂.along X (cov₂.along Y (fun z => φ z (σ z))) x -
          cov₂.along X (fun z => φ z (cov₁.along Y σ z)) x -
          (cov₂.along Y (fun z => φ z (cov₁.along X σ z)) x -
            φ x (cov₁.along Y (cov₁.along X σ) x)) := by
    rw [h1n, hpY, hpYQX]
    have hsubY := hsub (W := X) hP_Yφσ hφQY
    have hsubY' : cov₂.along X
        (fun y => cov₂.along Y (fun z => φ z (σ z)) y -
          φ y (cov₁.along Y σ y)) x =
        cov₂.along X (cov₂.along Y (fun z => φ z (σ z))) x -
          cov₂.along X (fun z => φ z (cov₁.along Y σ z)) x := by
      have hfunY :
          (fun y => cov₂.along Y (fun z => φ z (σ z)) y -
            φ y (cov₁.along Y σ y)) =
            cov₂.along Y (fun z => φ z (σ z)) -
              (fun y => φ y (cov₁.along Y σ y)) := by
        funext y
        rfl
      rw [hfunY]
      exact hsubY
    rw [hsubY']
  have h2' :
      (D (D.along X φ) x (Y x)) (σ x) =
        cov₂.along Y (cov₂.along X (fun z => φ z (σ z))) x -
          cov₂.along Y (fun z => φ z (cov₁.along X σ z)) x -
          (cov₂.along X (fun z => φ z (cov₁.along Y σ z)) x -
            φ x (cov₁.along X (cov₁.along Y σ) x)) := by
    rw [h2n, hpX, hpXQY]
    have hsubX := hsub (W := Y) hP_Xφσ hφQX
    have hsubX' : cov₂.along Y
        (fun y => cov₂.along X (fun z => φ z (σ z)) y -
          φ y (cov₁.along X σ y)) x =
        cov₂.along Y (cov₂.along X (fun z => φ z (σ z))) x -
          cov₂.along Y (fun z => φ z (cov₁.along X σ z)) x := by
      have hfunX :
          (fun y => cov₂.along X (fun z => φ z (σ z)) y -
            φ y (cov₁.along X σ y)) =
            cov₂.along X (fun z => φ z (σ z)) -
              (fun y => φ y (cov₁.along X σ y)) := by
        funext y
        rfl
      rw [hfunX]
      exact hsubX
    rw [hsubX']
  have h3 :
      D.along B φ x (σ x) =
        cov₂.along B (fun z => φ z (σ z)) x -
          φ x (cov₁.along B σ x) := by
    simpa [D, CovariantDerivative.along] using
      hprodAt φ σ B (hφ x) (hσ x)
  have hcurvD :
      D.curvatureAux X Y φ x (σ x) =
        (D (D.along Y φ) x (X x)) (σ x) -
          (D (D.along X φ) x (Y x)) (σ x) -
          (D.along B φ x) (σ x) := by
    simp only [CovariantDerivative.curvatureAux, CovariantDerivative.along,
      Pi.sub_apply, sub_apply, B]
  rw [hcurvD, h1', h2', h3]
  simp [CovariantDerivative.curvatureAux, CovariantDerivative.along, B]
  simp only [map_sub, map_add, sub_eq_add_neg]
  abel

end CovariantDerivative
