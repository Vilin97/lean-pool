/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.HomEvaluation

/-!
# Curvature under an affine connection change

This file records the raw, pointwise curvature expansion for adding an
endomorphism-valued one-form to a tangent-bundle connection.  It keeps the
first derivative of the one-form as an explicit covariant-derivative
expression, so its argument order is visible at the use site.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 2 M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TCorr" =>
  (fun x : M ↦ TM x →L[ℝ] TM x →L[ℝ] TM x)

/-- The covariant derivative of an endomorphism-valued one-form, evaluated
on three moving tangent fields.  The arguments after `A` are ordered as
`(X, Z, Y)`: `X` is the derivative direction, `Z` is the differentiated
vector, and `Y` is the one-form direction. -/
def covariantDerivativeOneFormAlong
    (cov : CovariantDerivative I E TM) (A : ∀ x : M, TCorr x)
    (X Z Y : ∀ x : M, TM x) (x : M) : TM x :=
  cov.along X (fun y ↦ A y (Z y) (Y y)) x -
    A x (Z x) (cov.along X Y x) - A x (cov.along X Z x) (Y x)

/-- The raw curvature change formula
`R(cov + A) = R(cov) + d_cov A + A ∧ A`.

`curvatureAux X Y Z` uses the conventional curvature order
`R(X,Y) Z`.  In the correction `A x z xdir`, `z` is the differentiated
vector and `xdir` is the connection direction, matching
`CovariantDerivative.addOneForm`.  The torsion-free hypothesis removes the
otherwise present `A(Z, T(X,Y))` term.  The remaining four
differentiability hypotheses are exactly what permits the base connection to
distribute over the two sums created by the changed connection. -/
theorem curvatureAux_addOneForm_apply
    (cov : CovariantDerivative I E TM) (A : ∀ x : M, TCorr x)
    {X Y Z : ∀ x : M, TM x} {x : M}
    (hTorsionFree : cov.torsion = 0)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hcovYZ : MDiffAt (T% (cov.along Y Z)) x)
    (hcovXZ : MDiffAt (T% (cov.along X Z)) x)
    (hAZY : MDiffAt (T% (fun y ↦ A y (Z y) (Y y))) x)
    (hAZX : MDiffAt (T% (fun y ↦ A y (Z y) (X y))) x) :
    (CovariantDerivative.addOneForm cov A).curvatureAux X Y Z x =
      cov.curvatureAux X Y Z x +
        covariantDerivativeOneFormAlong cov A X Z Y x -
        covariantDerivativeOneFormAlong cov A Y Z X x +
        A x (A x (Z x) (Y x)) (X x) -
        A x (A x (Z x) (X x)) (Y x) := by
  let covA := CovariantDerivative.addOneForm cov A
  have hAlongA (W σ : ∀ y : M, TM y) :
      covA.along W σ = cov.along W σ + fun y ↦ A y (σ y) (W y) := by
    funext y
    rfl
  have hfirst :
      cov.along X (covA.along Y Z) x =
        cov.along X (cov.along Y Z) x +
          cov.along X (fun y ↦ A y (Z y) (Y y)) x := by
    rw [hAlongA Y Z]
    exact cov.along_add_right_apply hcovYZ hAZY
  have hsecond :
      cov.along Y (covA.along X Z) x =
        cov.along Y (cov.along X Z) x +
          cov.along Y (fun y ↦ A y (Z y) (X y)) x := by
    rw [hAlongA X Z]
    exact cov.along_add_right_apply hcovXZ hAZX
  have hBracket :
      cov.along X Y x - cov.along Y X x = VectorField.mlieBracket I X Y x := by
    simpa [CovariantDerivative.along] using
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp hTorsionFree
        (X := X) (Y := Y) (x := x) hX hY
  rw [CovariantDerivative.curvatureAux_apply,
    CovariantDerivative.curvatureAux_apply]
  rw [show covA.along X (covA.along Y Z) x =
      cov.along X (covA.along Y Z) x +
        A x (covA.along Y Z x) (X x) by rfl,
    show covA.along Y (covA.along X Z) x =
      cov.along Y (covA.along X Z) x +
        A x (covA.along X Z x) (Y x) by rfl,
    show covA.along (VectorField.mlieBracket I X Y) Z x =
      cov.along (VectorField.mlieBracket I X Y) Z x +
        A x (Z x) (VectorField.mlieBracket I X Y x) by rfl,
    hfirst, hsecond]
  simp only [hAlongA Y Z, hAlongA X Z, Pi.add_apply, map_add, add_apply]
  rw [← hBracket]
  simp [covariantDerivativeOneFormAlong, map_add]
  abel

section Tensor

variable [T2Space M] [IsManifold I ∞ M]
  [hTangentTwo : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TEnd" => (fun x : M ↦ TM x →L[ℝ] TM x)

/-- The induced hom connections below use the tangent bundle both as a
source and as a target.  Install the lowered bundle regularity explicitly:
typeclass search does not lower the given `C²` bundle structure by itself. -/
local instance tangentOne : ContMDiffVectorBundle 1 E TM I :=
  ContMDiffVectorBundle.of_le (F := E) (E := TM) (IB := I)
    (m := 1) (n := 2) (by norm_num)

/-- The endomorphism bundle inherits the tangent bundle's `C²` structure. -/
local instance endTwo : ContMDiffVectorBundle 2 (E →L[ℝ] E) TEnd I :=
  ContMDiffVectorBundle.continuousLinearMap

/-- The outer induced hom connection only needs the `C¹` endomorphism
bundle structure. -/
local instance endOne : ContMDiffVectorBundle 1 (E →L[ℝ] E) TEnd I :=
  ContMDiffVectorBundle.of_le (F := E →L[ℝ] E) (E := TEnd) (IB := I)
    (m := 1) (n := 2) (by norm_num)

/-- The connection on endomorphism-valued one-forms induced by `cov` in all
three tangent slots.  Its arguments are `(derivative direction, differentiated
vector, one-form direction)`. -/
noncomputable def covariantDerivativeOneForm
    (cov : CovariantDerivative I E TM) (A : ∀ x : M, TCorr x) (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x := by
  let DEnd := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _
    TM TM
      _ _ _ _ (fun _ ↦ inferInstanceAs (FiniteDimensional ℝ E)) _ _
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hTangentTwo tangentOne cov cov
  exact @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E (E →L[ℝ] E) _ _ _ _ _
    TM TEnd
      _ (Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) E TM E TM)
        _ _ (fun _ ↦ inferInstanceAs (FiniteDimensional ℝ E))
        (fun _ ↦ ContinuousLinearMap.toNormedAddCommGroup)
        (fun y ↦ @ContinuousLinearMap.toNormedSpace
          ℝ ℝ (TM y) (TM y) _ _ _ _
          (PoincareCurvature.instNormedSpaceTangentSpace I y)
          (PoincareCurvature.instNormedSpaceTangentSpace I y)
          (RingHom.id ℝ) _ ℝ _ (PoincareCurvature.instNormedSpaceTangentSpace I y)
          (by
            constructor
            intro a b v
            calc
              a • b • v = (a * b) • v := (mul_smul a b v).symm
              _ = (b * a) • v := by rw [mul_comm]
              _ = b • a • v := mul_smul b a v))
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    (Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ) E TM E TM)
    (Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ) E TM E TM)
    hTangentTwo endOne cov DEnd A x

/-- Evaluating the induced connection on a one-form yields the expected
three-slot covariant derivative. -/
theorem covariantDerivativeOneForm_apply_eq_along
    (cov : CovariantDerivative I E TM) (A : ∀ x : M, TCorr x)
    {X Y Z : ∀ x : M, TM x} {x : M}
    (hA : MDiffAt
      (fun y ↦ TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y (A y)) x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    covariantDerivativeOneForm cov A x (X x) (Z x) (Y x) =
      covariantDerivativeOneFormAlong cov A X Z Y x := by
  let DEnd := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _
    TM TM
      _ _ _ _ (fun _ ↦ inferInstanceAs (FiniteDimensional ℝ E)) _ _
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hTangentTwo tangentOne cov cov
  let Dcorr := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E (E →L[ℝ] E) _ _ _ _ _
    TM TEnd
      _ (Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) E TM E TM)
        _ _ (fun _ ↦ inferInstanceAs (FiniteDimensional ℝ E))
        (fun _ ↦ ContinuousLinearMap.toNormedAddCommGroup)
        (fun y ↦ @ContinuousLinearMap.toNormedSpace
          ℝ ℝ (TM y) (TM y) _ _ _ _
          (PoincareCurvature.instNormedSpaceTangentSpace I y)
          (PoincareCurvature.instNormedSpaceTangentSpace I y)
          (RingHom.id ℝ) _ ℝ _ (PoincareCurvature.instNormedSpaceTangentSpace I y)
          (by
            constructor
            intro a b v
            calc
              a • b • v = (a * b) • v := (mul_smul a b v).symm
              _ = (b * a) • v := by rw [mul_comm]
              _ = b • a • v := mul_smul b a v))
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    (Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ) E TM E TM)
    (Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ) E TM E TM)
    hTangentTwo endOne cov DEnd
  have hAZ : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) y (A y (Z y))) x :=
    hA.clm_bundle_apply hZ
  have hOuter := @inducedHomCovariantDerivative_apply_section_general
    E _ _ H _ I M _ _ _ _ _ _
    E (E →L[ℝ] E) _ _ _ _ _ _
    TM TEnd
      _ (Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) E TM E TM)
        _ _ (fun _ ↦ inferInstanceAs (FiniteDimensional ℝ E))
        (fun _ ↦ ContinuousLinearMap.toNormedAddCommGroup)
        (fun y ↦ @ContinuousLinearMap.toNormedSpace
          ℝ ℝ (TM y) (TM y) _ _ _ _
          (PoincareCurvature.instNormedSpaceTangentSpace I y)
          (PoincareCurvature.instNormedSpaceTangentSpace I y)
          (RingHom.id ℝ) _ ℝ _ (PoincareCurvature.instNormedSpaceTangentSpace I y)
          (by
            constructor
            intro a b v
            calc
              a • b • v = (a * b) • v := (mul_smul a b v).symm
              _ = (b * a) • v := by rw [mul_comm]
              _ = b • a • v := mul_smul b a v))
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    (Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ) E TM E TM)
    (Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ) E TM E TM)
    hTangentTwo endTwo cov DEnd A Z x hA hZ (X x)
  have hInner := @inducedHomCovariantDerivative_apply_section_general
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _ _
    TM TM
      _ _ _ _ (fun _ ↦ inferInstanceAs (FiniteDimensional ℝ E)) _ _
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hTangentTwo hTangentTwo cov cov (fun y ↦ A y (Z y)) Y x hAZ hY (X x)
  unfold covariantDerivativeOneForm
  change (Dcorr A x (X x)) (Z x) (Y x) = _
  rw [hOuter]
  change (DEnd (fun y ↦ A y (Z y)) x (X x)) (Y x) -
      A x (cov Z x (X x)) (Y x) = _
  rw [hInner]
  unfold covariantDerivativeOneFormAlong
  unfold CovariantDerivative.along
  rfl

/-- The bundled, pointwise curvature change formula for a torsion-free
background connection.  This is the fibrewise form of
`R(cov + A) = R(cov) + d_cov A + A ∧ A`.

The arguments of `covariantDerivativeOneForm cov A x` are, in order,
the derivative direction, the vector being differentiated, and the one-form
direction.  Thus the two first-order terms are
`(∇_u A)(w,v) - (∇_v A)(w,u)`. -/
theorem curvatureTensor_addOneForm_apply
    (cov : CovariantDerivative I E TM) (A : ∀ x : M, TCorr x)
    [ContMDiffCovariantDerivative cov 1]
    [ContMDiffCovariantDerivative (CovariantDerivative.addOneForm cov A) 1]
    (hTorsionFree : cov.torsion = 0)
    (hA : ∀ y, MDiffAt
      (fun z ↦ TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) z (A z)) y)
    (x : M) (u v w : TM x) :
    (CovariantDerivative.addOneForm cov A).curvatureTensor x u v w =
      cov.curvatureTensor x u v w +
        covariantDerivativeOneForm cov A x u w v -
        covariantDerivativeOneForm cov A x v w u +
        A x (A x w v) u - A x (A x w u) v := by
  let X : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x u
  let Y : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x v
  let Z : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x w
  have hXone : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)) := by
    simpa [X] using smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u
  have hYone : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)) := by
    simpa [Y] using smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v
  have hZtwo : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Z y)) := by
    simpa [Z] using smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x w
  have hX : MDiffAt (T% X) x :=
    (hXone x).mdifferentiableAt one_ne_zero
  have hY : MDiffAt (T% Y) x :=
    (hYone x).mdifferentiableAt one_ne_zero
  have hZ : MDiffAt (T% Z) x :=
    ((hZtwo.of_le (by norm_num) x).mdifferentiableAt one_ne_zero)
  have hcovYZ : MDiffAt (T% (cov.along Y Z)) x := by
    exact (cov.contMDiff_along hYone hZtwo x).mdifferentiableAt one_ne_zero
  have hcovXZ : MDiffAt (T% (cov.along X Z)) x := by
    exact (cov.contMDiff_along hXone hZtwo x).mdifferentiableAt one_ne_zero
  have hAZ : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) y (A y (Z y))) x :=
    (hA x).clm_bundle_apply hZ
  have hAZY : MDiffAt (T% (fun y ↦ A y (Z y) (Y y))) x :=
    hAZ.clm_bundle_apply hY
  have hAZX : MDiffAt (T% (fun y ↦ A y (Z y) (X y))) x :=
    hAZ.clm_bundle_apply hX
  have hDA_X :
      covariantDerivativeOneForm cov A x u w v =
        covariantDerivativeOneFormAlong cov A X Z Y x := by
    simpa [X, Y, Z, smoothExtend_apply] using
      (covariantDerivativeOneForm_apply_eq_along (I := I) cov A
        (X := X) (Y := Y) (Z := Z) (hA x) hY hZ)
  have hDA_Y :
      covariantDerivativeOneForm cov A x v w u =
        covariantDerivativeOneFormAlong cov A Y Z X x := by
    simpa [X, Y, Z, smoothExtend_apply] using
      (covariantDerivativeOneForm_apply_eq_along (I := I) cov A
        (X := Y) (Y := X) (Z := Z) (hA x) hX hZ)
  have hraw := curvatureAux_addOneForm_apply cov A hTorsionFree hX hY hcovYZ hcovXZ hAZY hAZX
  rw [hDA_X, hDA_Y]
  simpa [curvatureTensor_apply, X, Y, Z, smoothExtend_apply] using hraw

end Tensor

end CovariantDerivative
