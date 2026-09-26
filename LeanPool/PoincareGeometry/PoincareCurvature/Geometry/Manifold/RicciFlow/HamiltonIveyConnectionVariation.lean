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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TimeDependent
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyKoszul

/-!
# Curvature variation from connection variation

The time-dependent geometry API is intentionally slicewise: it does not silently identify a
time derivative with a derivative of the spatial connection coefficients.  This file isolates
the precise connection-variation rule needed to differentiate curvature.  Given that rule for
the connection acting on time-dependent sections, the time derivative of the actual curvature
tensor follows directly from its commutator definition.

The metric-to-Levi-Civita-connection variation is a separate geometric step; it is not assumed
or claimed here.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentCovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [IsManifold I (minSmoothness ℝ 2) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- A pointwise candidate A for the first time variation of a connection.  Its defining rule
includes the ordinary connection action on the time derivative of a moving section.  This is the
exact chain rule needed when differentiating the nested covariant derivatives in the curvature
commutator.  No bilinearity or metric-variation formula for A is asserted here. -/
def HasConnectionTimeVariationAt
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (A : ∀ x : M, TM x → TM x → TM x) (t : ℝ) : Prop :=
  ∀ (X : Π x : M, TM x), (∀ x, MDiffAt (T% X) x) →
    ∀ (σ : ℝ → Π x : M, TM x) (σdot : Π x : M, TM x),
      (∀ τ x, MDiffAt (T% (σ τ)) x) →
      (∀ x, MDiffAt (T% σdot) x) →
      (∀ x, HasDerivAt (fun τ : ℝ => σ τ x) (σdot x) t) →
      ∀ x, HasDerivAt
        (fun τ : ℝ => (cov τ).along X (σ τ) x)
        ((cov t).along X σdot x + A x (X x) (σ t x)) t

/-- The connection-variation rule for a constant section is the pointwise time derivative of
the connection applied to that section. -/
theorem hasDerivAt_along_const_of_hasConnectionTimeVariationAt
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (A : ∀ x : M, TM x → TM x → TM x) {t : ℝ}
    (hvariation : HasConnectionTimeVariationAt (I := I) (M := M) cov A t)
    (X σ : Π x : M, TM x) (hX : ∀ x, MDiffAt (T% X) x)
    (hσ : ∀ x, MDiffAt (T% σ) x) :
    ∀ x, HasDerivAt
      (fun τ : ℝ => (cov τ).along X σ x)
      (A x (X x) (σ x)) t := by
  intro x
  have hconst : ∀ y : M, HasDerivAt (fun _ : ℝ => σ y) 0 t := by
    intro y
    exact hasDerivAt_const (x := t) (c := σ y)
  have hzeroSpace : ∀ y, MDiffAt (T% (fun z : M => (0 : TM z))) y := by
    intro y
    exact mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := E) (E := TM) (x := y)
  have h := hvariation X hX (fun _ : ℝ => σ) (fun _ : M => 0)
    (by
      intro _ y
      exact hσ y) hzeroSpace hconst x
  have hzeroAlong : (cov t).along X (fun y : M => (0 : TM y)) x = 0 := by
    change ((cov t) (fun y : M => (0 : TM y)) x) (X x) = 0
    have hcovZero :
        (cov t) (fun y : M => (0 : TM y)) =
          (0 : Π y : M, TM y →L[ℝ] TM y) := by
      exact _root_.CovariantDerivative.zero (cov := cov t)
    rw [hcovZero]
    simp
  rw [hzeroAlong] at h
  simpa using h

/-- The actual curvature-tensor velocity induced by a connection velocity A.  The vector
fields used here are the canonical smooth extensions used in the repository's genuine
curvature-tensor definition. -/
noncomputable def curvatureTensorTimeVelocity
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (A : ∀ x : M, TM x → TM x → TM x)
    (t : ℝ) (x : M) (a b c : TM x) : TM x :=
  let X := smoothExtend (I := I) (F := E) (V := TM) x a
  let Y := smoothExtend (I := I) (F := E) (V := TM) x b
  let Z := smoothExtend (I := I) (F := E) (V := TM) x c
  ((cov t).along X (fun y => A y (Y y) (Z y)) x +
      A x (X x) ((cov t).along Y Z x)) -
    ((cov t).along Y (fun y => A y (X y) (Z y)) x +
      A x (Y x) ((cov t).along X Z x)) -
    A x (VectorField.mlieBracket I X Y x) (Z x)

/-- Differentiating the actual curvature commutator gives the curvature variation formula.
The proof uses the variation rule for the connection on the two nested covariant derivatives and
on the Lie-bracket term; it does not postulate a derivative of the curvature tensor. -/
theorem hasDerivAt_curvatureTensor_of_hasConnectionTimeVariationAt
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (A : ∀ x : M, TM x → TM x → TM x) {t : ℝ} (x : M)
    (hvariation : HasConnectionTimeVariationAt (I := I) (M := M) cov A t)
    (hA : ∀ (X Y : Π y : M, TM y),
      (∀ y, MDiffAt (T% X) y) → (∀ y, MDiffAt (T% Y) y) →
        ∀ y, MDiffAt (T% (fun z => A z (X z) (Y z))) y)
    (a b c : TM x) :
    HasDerivAt
      (fun τ : ℝ =>
        TimeDependentCovariantDerivative.curvatureTensor
          (I := I) (M := M) cov hcov τ x a b c)
      (curvatureTensorTimeVelocity (I := I) (M := M) cov A t x a b c) t := by
  let X : Π y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x a
  let Y : Π y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x b
  let Z : Π y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x c
  have hX₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% X) := by
    simpa [X] using smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x a
  have hY₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Y) := by
    simpa [Y] using smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x b
  have hZ₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z) := by
    simpa [Z] using smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x c
  have hX₁ := hX₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hY₁ := hY₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hZ₁ := hZ₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hX : ∀ y, MDiffAt (T% X) y := fun y =>
    (hX₁ y).mdifferentiableAt one_ne_zero
  have hY : ∀ y, MDiffAt (T% Y) y := fun y =>
    (hY₁ y).mdifferentiableAt one_ne_zero
  have hZ : ∀ y, MDiffAt (T% Z) y := fun y =>
    (hZ₁ y).mdifferentiableAt one_ne_zero
  have hbracket : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (T% (VectorField.mlieBracket I X Y)) := by
    simpa using (ContDiff.mlieBracket_vectorField (I := I)
      (m := (1 : ℕ∞)) (n := (2 : ℕ∞)) hX₂ hY₂ (by norm_num))
  have hbracket' : ∀ y, MDiffAt (T% (VectorField.mlieBracket I X Y)) y :=
    fun y => (hbracket y).mdifferentiableAt one_ne_zero
  have hAYZ : ∀ y, MDiffAt (T% (fun z => A z (Y z) (Z z))) y :=
    hA Y Z hY hZ
  have hAXZ : ∀ y, MDiffAt (T% (fun z => A z (X z) (Z z))) y :=
    hA X Z hX hZ
  have hinner₁ :
      ∀ y, HasDerivAt (fun τ : ℝ => (cov τ).along Y Z y)
        (A y (Y y) (Z y)) t :=
    hasDerivAt_along_const_of_hasConnectionTimeVariationAt
      (I := I) (M := M) cov A hvariation Y Z hY hZ
  have hinner₂ :
      ∀ y, HasDerivAt (fun τ : ℝ => (cov τ).along X Z y)
        (A y (X y) (Z y)) t :=
    hasDerivAt_along_const_of_hasConnectionTimeVariationAt
      (I := I) (M := M) cov A hvariation X Z hX hZ
  have hspace₁ : ∀ τ y, MDiffAt
      (T% (fun z => (cov τ).along Y Z z)) y := by
    intro τ y
    letI := hcov τ
    have htemp : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (T% ((cov τ).along Y Z)) :=
      (cov τ).contMDiff_along hY₁ hZ₂
    exact (htemp y).mdifferentiableAt one_ne_zero
  have hspace₂ : ∀ τ y, MDiffAt
      (T% (fun z => (cov τ).along X Z z)) y := by
    intro τ y
    letI := hcov τ
    have htemp : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (T% ((cov τ).along X Z)) :=
      (cov τ).contMDiff_along hX₁ hZ₂
    exact (htemp y).mdifferentiableAt one_ne_zero
  have houter₁ :
      HasDerivAt
        (fun τ : ℝ => (cov τ).along X (fun y => (cov τ).along Y Z y) x)
        ((cov t).along X (fun y => A y (Y y) (Z y)) x +
          A x (X x) ((cov t).along Y Z x)) t := by
    exact hvariation X hX (fun τ y => (cov τ).along Y Z y)
      (fun y => A y (Y y) (Z y)) hspace₁ hAYZ hinner₁ x
  have houter₂ :
      HasDerivAt
        (fun τ : ℝ => (cov τ).along Y (fun y => (cov τ).along X Z y) x)
        ((cov t).along Y (fun y => A y (X y) (Z y)) x +
          A x (Y x) ((cov t).along X Z x)) t := by
    exact hvariation Y hY (fun τ y => (cov τ).along X Z y)
      (fun y => A y (X y) (Z y)) hspace₂ hAXZ hinner₂ x
  have houter₃ :
      HasDerivAt
        (fun τ : ℝ => (cov τ).along (VectorField.mlieBracket I X Y) Z x)
        (A x (VectorField.mlieBracket I X Y x) (Z x)) t := by
    exact hasDerivAt_along_const_of_hasConnectionTimeVariationAt
      (I := I) (M := M) cov A hvariation
      (VectorField.mlieBracket I X Y) Z hbracket' hZ x
  have hraw :
      HasDerivAt
        (fun τ : ℝ => (cov τ).curvatureAux X Y Z x)
        (((cov t).along X (fun y => A y (Y y) (Z y)) x +
            A x (X x) ((cov t).along Y Z x)) -
          ((cov t).along Y (fun y => A y (X y) (Z y)) x +
            A x (Y x) ((cov t).along X Z x)) -
          A x (VectorField.mlieBracket I X Y x) (Z x)) t := by
    change HasDerivAt
      (fun τ : ℝ =>
        (cov τ).along X ((cov τ).along Y Z) x -
          (cov τ).along Y ((cov τ).along X Z) x -
          (cov τ).along (VectorField.mlieBracket I X Y) Z x)
      _ t
    exact (houter₁.sub houter₂).sub houter₃
  change HasDerivAt
    (fun τ : ℝ =>
      TimeDependentCovariantDerivative.curvatureTensor
        (I := I) (M := M) cov hcov τ x a b c)
    (curvatureTensorTimeVelocity (I := I) (M := M) cov A t x a b c) t
  simpa [curvatureTensorTimeVelocity, X, Y, Z,
    TimeDependentCovariantDerivative.curvatureTensor_apply,
    CovariantDerivative.curvatureTensor_apply] using hraw

end CovariantDerivative.TimeDependentCovariantDerivative

end
