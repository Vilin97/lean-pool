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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Bianchi identities

This file proves the first Bianchi identity for torsion-free affine connections on
the tangent bundle, both for smooth vector fields and for the bundled curvature
tensor built from canonical smooth extensions. It also proves a raw second
Bianchi identity on smooth tangent vector fields, avoiding tensor-bundle
connection infrastructure.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

section FirstBianchi

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]

private lemma along_sub_right_apply {x : M}
    {X σ τ : Π x : M, TM x} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    cov.along X (σ - τ) x = cov.along X σ x - cov.along X τ x := by
  have hsub : σ - τ = σ + ((fun _ : M ↦ (-1 : ℝ)) • τ) := by
    ext y
    simp [sub_eq_add_neg]
  rw [hsub]
  have hsmul : MDiffAt (T% ((fun _ : M ↦ (-1 : ℝ)) • τ)) x := by
    simpa using
      (MDifferentiableAt.smul_section (f := fun _ : M ↦ (-1 : ℝ)) (s := τ)
        mdifferentiableAt_const hτ)
  rw [cov.along_add_right_apply hσ hsmul]
  have hnegApply : cov.along X ((fun _ : M ↦ (-1 : ℝ)) • τ) x = -cov.along X τ x := by
    calc
      cov.along X ((fun _ : M ↦ (-1 : ℝ)) • τ) x = -cov.along X τ x + 0 := by
        simpa [mvfderiv] using
          (cov.along_smul_right_apply (x := x) (f := fun _ : M ↦ (-1 : ℝ)) (X := X)
            (σ := τ) mdifferentiableAt_const hτ)
      _ = -cov.along X τ x := by simp
  rw [hnegApply]
  simp [sub_eq_add_neg]

/-- For torsion-free affine connections, the covariant-derivative commutator on vector fields is
the Lie bracket. -/
lemma along_sub_eq_mlieBracket_of_torsion_eq_zero
    (hT : cov.torsion = 0)
    {X Y : Π x : M, TM x}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y))) :
    cov.along X Y - cov.along Y X = VectorField.mlieBracket I X Y := by
  ext x
  simpa [CovariantDerivative.along] using
    (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp hT
      (X := X) (Y := Y) (x := x)
      ((hX x).mdifferentiableAt one_ne_zero)
      ((hY x).mdifferentiableAt one_ne_zero)

private lemma cyclic_mlieBracket_apply_eq_zero
    {X Y Z : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y))) :
    VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x +
      VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x +
      VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x = 0 := by
  have hXMin :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
        (fun y ↦ TotalSpace.mk' E y (X y)) x :=
    (hX x).of_le (by simp)
  have hYMin :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
        (fun y ↦ TotalSpace.mk' E y (Y y)) x :=
    (hY x).of_le (by simp)
  have hZMin :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
        (fun y ↦ TotalSpace.mk' E y (Z y)) x :=
    (hZ x).of_le (by simp)
  have hZXCont :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (VectorField.mlieBracket I Z X y)) x := by
    simpa using
      (ContMDiffAt.mlieBracket_vectorField (I := I) (m := (1 : ℕ∞)) (n := (2 : ℕ∞))
        (hZ x) (hX x) (by norm_num))
  have hZX :
      MDiffAt (T% (VectorField.mlieBracket I Z X)) x := by
    exact hZXCont.mdifferentiableAt one_ne_zero
  have hJac :=
    VectorField.leibniz_identity_mlieBracket_apply (I := I) (x := x) hXMin hYMin hZMin
  have hSwap₁ :
      VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x =
        -VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x := by
    simpa using
      (VectorField.mlieBracket_swap_apply
        (I := I) (V := VectorField.mlieBracket I X Y) (W := Z) (x := x))
  have hSwap₂ :
      VectorField.mlieBracket I Y (VectorField.mlieBracket I X Z) x =
        -VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x := by
    have hXZSwap : VectorField.mlieBracket I X Z = -VectorField.mlieBracket I Z X := by
      simpa using (VectorField.mlieBracket_swap (I := I) (V := X) (W := Z))
    rw [hXZSwap]
    simpa using
      (VectorField.mlieBracket_const_smul_right
        (I := I) (x := x) (V := Y) (W := VectorField.mlieBracket I Z X)
        (c := (-1 : ℝ)) hZX)
  calc
    VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x +
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x +
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x
      = (-VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x +
          -VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x) +
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x +
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x := by
          rw [hJac, hSwap₁, hSwap₂]
    _ = 0 := by
      abel_nf

/-- Pointwise first Bianchi identity for the raw curvature commutator of a torsion-free affine
connection on the tangent bundle. -/
theorem firstBianchiAux_apply_of_torsion_eq_zero
    (hT : cov.torsion = 0)
    {X Y Z : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y))) :
    cov.curvatureAux X Y Z x + cov.curvatureAux Y Z X x + cov.curvatureAux Z X Y x = 0 := by
  have hX₁ := hX.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)
  have hY₁ := hY.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)
  have hZ₁ := hZ.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)
  have hAlongYZ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along Y Z y)) :=
    cov.contMDiff_along (n := 1) hY₁ hZ
  have hAlongZY :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along Z Y y)) :=
    cov.contMDiff_along (n := 1) hZ₁ hY
  have hAlongZX :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along Z X y)) :=
    cov.contMDiff_along (n := 1) hZ₁ hX
  have hAlongXZ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along X Z y)) :=
    cov.contMDiff_along (n := 1) hX₁ hZ
  have hAlongXY :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along X Y y)) :=
    cov.contMDiff_along (n := 1) hX₁ hY
  have hAlongYX :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along Y X y)) :=
    cov.contMDiff_along (n := 1) hY₁ hX
  have hYZ := cov.along_sub_eq_mlieBracket_of_torsion_eq_zero hT hY₁ hZ₁
  have hZX := cov.along_sub_eq_mlieBracket_of_torsion_eq_zero hT hZ₁ hX₁
  have hXY := cov.along_sub_eq_mlieBracket_of_torsion_eq_zero hT hX₁ hY₁
  have hBracketYZ₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (VectorField.mlieBracket I Y Z y)) := by
    simpa using
      (ContDiff.mlieBracket_vectorField (I := I) (m := (1 : ℕ∞)) (n := (2 : ℕ∞))
        hY hZ (by norm_num))
  have hBracketZX₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (VectorField.mlieBracket I Z X y)) := by
    simpa using
      (ContDiff.mlieBracket_vectorField (I := I) (m := (1 : ℕ∞)) (n := (2 : ℕ∞))
        hZ hX (by norm_num))
  have hBracketXY₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (VectorField.mlieBracket I X Y y)) := by
    simpa using
      (ContDiff.mlieBracket_vectorField (I := I) (m := (1 : ℕ∞)) (n := (2 : ℕ∞))
        hX hY (by norm_num))
  have hNested₁ :
      cov.along X (VectorField.mlieBracket I Y Z) x -
          cov.along (VectorField.mlieBracket I Y Z) X x =
        VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x := by
    simpa using
      congrArg (fun s => s x) <|
        cov.along_sub_eq_mlieBracket_of_torsion_eq_zero hT hX₁ hBracketYZ₁
  have hNested₂ :
      cov.along Y (VectorField.mlieBracket I Z X) x -
          cov.along (VectorField.mlieBracket I Z X) Y x =
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x := by
    simpa using
      congrArg (fun s => s x) <|
        cov.along_sub_eq_mlieBracket_of_torsion_eq_zero hT hY₁ hBracketZX₁
  have hNested₃ :
      cov.along Z (VectorField.mlieBracket I X Y) x -
          cov.along (VectorField.mlieBracket I X Y) Z x =
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x := by
    simpa using
      congrArg (fun s => s x) <|
        cov.along_sub_eq_mlieBracket_of_torsion_eq_zero hT hZ₁ hBracketXY₁
  calc
    cov.curvatureAux X Y Z x + cov.curvatureAux Y Z X x + cov.curvatureAux Z X Y x
      = (cov.along X (cov.along Y Z) x - cov.along Y (cov.along X Z) x -
          cov.along (VectorField.mlieBracket I X Y) Z x) +
        (cov.along Y (cov.along Z X) x - cov.along Z (cov.along Y X) x -
          cov.along (VectorField.mlieBracket I Y Z) X x) +
        (cov.along Z (cov.along X Y) x - cov.along X (cov.along Z Y) x -
           cov.along (VectorField.mlieBracket I Z X) Y x) := by
             simp [CovariantDerivative.curvatureAux]
    _ = cov.along X (cov.along Y Z - cov.along Z Y) x +
          cov.along Y (cov.along Z X - cov.along X Z) x +
          cov.along Z (cov.along X Y - cov.along Y X) x -
          cov.along (VectorField.mlieBracket I X Y) Z x -
          cov.along (VectorField.mlieBracket I Y Z) X x -
          cov.along (VectorField.mlieBracket I Z X) Y x := by
            rw [cov.along_sub_right_apply
                  ((hAlongYZ x).mdifferentiableAt one_ne_zero)
                  ((hAlongZY x).mdifferentiableAt one_ne_zero),
                cov.along_sub_right_apply
                  ((hAlongZX x).mdifferentiableAt one_ne_zero)
                  ((hAlongXZ x).mdifferentiableAt one_ne_zero),
                cov.along_sub_right_apply
                  ((hAlongXY x).mdifferentiableAt one_ne_zero)
                  ((hAlongYX x).mdifferentiableAt one_ne_zero)]
            abel_nf
    _ = cov.along X (VectorField.mlieBracket I Y Z) x +
          cov.along Y (VectorField.mlieBracket I Z X) x +
          cov.along Z (VectorField.mlieBracket I X Y) x -
          cov.along (VectorField.mlieBracket I X Y) Z x -
          cov.along (VectorField.mlieBracket I Y Z) X x -
          cov.along (VectorField.mlieBracket I Z X) Y x := by
            rw [hYZ, hZX, hXY]
    _ = (cov.along X (VectorField.mlieBracket I Y Z) x -
          cov.along (VectorField.mlieBracket I Y Z) X x) +
        (cov.along Y (VectorField.mlieBracket I Z X) x -
          cov.along (VectorField.mlieBracket I Z X) Y x) +
        (cov.along Z (VectorField.mlieBracket I X Y) x -
          cov.along (VectorField.mlieBracket I X Y) Z x) := by
            abel_nf
    _ = VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x +
          VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x +
          VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x := by
            rw [hNested₁, hNested₂, hNested₃]
    _ = 0 := cyclic_mlieBracket_apply_eq_zero (I := I) hX hY hZ

/-- Section-valued first Bianchi identity for torsion-free affine connections on the tangent
bundle. -/
theorem firstBianchiAux_of_torsion_eq_zero
    (hT : cov.torsion = 0)
    {X Y Z : Π x : M, TM x}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y))) :
    cov.curvatureAux X Y Z + cov.curvatureAux Y Z X + cov.curvatureAux Z X Y = 0 := by
  ext x
  exact cov.firstBianchiAux_apply_of_torsion_eq_zero hT hX hY hZ

/-- Pointwise first Bianchi identity for the bundled curvature tensor of a torsion-free affine
connection. -/
theorem firstBianchi_curvatureTensor_of_torsion_eq_zero
    (hT : cov.torsion = 0) (x : M) (u v w : TM x) :
    cov.curvatureTensor x u v w +
      cov.curvatureTensor x v w u +
      cov.curvatureTensor x w u v = 0 := by
  simpa [CovariantDerivative.curvatureTensor_apply] using
    cov.firstBianchiAux_apply_of_torsion_eq_zero (hT := hT) (x := x)
      (X := smoothExtend (I := I) (F := E) (V := TM) x u)
      (Y := smoothExtend (I := I) (F := E) (V := TM) x v)
      (Z := smoothExtend (I := I) (F := E) (V := TM) x w)
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x u)
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x v)
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x w)

end FirstBianchi

section SecondBianchi

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
  [IsManifold I (minSmoothness ℝ 2) M] [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M] [IsManifold I ((3 : ℕ∞) + 1) M]

/-- The raw covariant derivative of the raw curvature operator on tangent vector fields. -/
def secondBianchiAux
    (X Y Z W : Π x : M, TM x) : Π x : M, TM x :=
  cov.along X (cov.curvatureAux Y Z W) -
    cov.curvatureAux (cov.along X Y) Z W -
    cov.curvatureAux Y (cov.along X Z) W -
    cov.curvatureAux Y Z (cov.along X W)

@[simp]
lemma secondBianchiAux_apply
    (X Y Z W : Π x : M, TM x) (x : M) :
    cov.secondBianchiAux X Y Z W x =
      cov.along X (cov.curvatureAux Y Z W) x -
        cov.curvatureAux (cov.along X Y) Z W x -
        cov.curvatureAux Y (cov.along X Z) W x -
        cov.curvatureAux Y Z (cov.along X W) x := rfl

private lemma mdifferentiableAt_along_of_contMDiff
    {X σ : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (σ y))) :
    MDiffAt (T% (cov.along X σ)) x := by
  exact ((cov.contMDiff_along (n := 1) hX hσ) x).mdifferentiableAt one_ne_zero

private lemma curvatureAux_sub_left_apply
    {X X' Y W : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hX' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X' y)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (W y))) :
    cov.curvatureAux (X - X') Y W x =
      cov.curvatureAux X Y W x - cov.curvatureAux X' Y W x := by
  have hXW : MDiffAt (T% (cov.along X W)) x := cov.mdifferentiableAt_along_of_contMDiff hX hW
  have hX'W : MDiffAt (T% (cov.along X' W)) x := cov.mdifferentiableAt_along_of_contMDiff hX' hW
  have hXx : MDiffAt (T% X) x := (hX x).mdifferentiableAt one_ne_zero
  have hX'x : MDiffAt (T% X') x := (hX' x).mdifferentiableAt one_ne_zero
  have hNegX'x : MDiffAt (T% (-X')) x := mdifferentiableAt_neg_section hX'x
  have h1 :
      cov.along (X - X') (cov.along Y W) x =
        cov.along X (cov.along Y W) x - cov.along X' (cov.along Y W) x := by
    exact congrArg (fun s => s x) (cov.along_sub_left X X' (cov.along Y W))
  have h2 :
      cov.along Y (cov.along (X - X') W) x =
        cov.along Y (cov.along X W) x - cov.along Y (cov.along X' W) x := by
    calc
      cov.along Y (cov.along (X - X') W) x =
          cov.along Y (cov.along X W - cov.along X' W) x := by
            exact congrArg (fun s ↦ cov.along Y s x) (cov.along_sub_left X X' W)
      _ = cov.along Y (cov.along X W) x - cov.along Y (cov.along X' W) x :=
            cov.along_sub_right_apply (x := x) (X := Y) hXW hX'W
  have hBracketSub :
      VectorField.mlieBracket I (X - X') Y x =
        VectorField.mlieBracket I X Y x - VectorField.mlieBracket I X' Y x := by
    have hConst :
        VectorField.mlieBracket I (-X') Y x = -VectorField.mlieBracket I X' Y x := by
      simpa using
        (VectorField.mlieBracket_const_smul_left
          (I := I) (x := x) (V := X') (W := Y) (c := (-1 : ℝ)) hX'x)
    calc
      VectorField.mlieBracket I (X - X') Y x =
          VectorField.mlieBracket I (X + -X') Y x := by
            rw [sub_eq_add_neg]
      _ = VectorField.mlieBracket I X Y x + VectorField.mlieBracket I (-X') Y x :=
          VectorField.mlieBracket_add_left (I := I) (V := X) (V₁ := -X') (W := Y) hXx hNegX'x
      _ = VectorField.mlieBracket I X Y x - VectorField.mlieBracket I X' Y x := by
          rw [hConst]
          abel_nf
  have h3 :
      cov.along (VectorField.mlieBracket I (X - X') Y) W x =
        cov.along (VectorField.mlieBracket I X Y) W x -
          cov.along (VectorField.mlieBracket I X' Y) W x := by
    calc
      cov.along (VectorField.mlieBracket I (X - X') Y) W x
          = cov.along (VectorField.mlieBracket I X Y - VectorField.mlieBracket I X' Y) W x := by
              simp [hBracketSub]
      _ = cov.along (VectorField.mlieBracket I X Y) W x -
            cov.along (VectorField.mlieBracket I X' Y) W x := by
              exact congrArg (fun s => s x)
                (cov.along_sub_left
                  (VectorField.mlieBracket I X Y) (VectorField.mlieBracket I X' Y) W)
  calc
    cov.curvatureAux (X - X') Y W x
        = cov.along (X - X') (cov.along Y W) x -
            cov.along Y (cov.along (X - X') W) x -
            cov.along (VectorField.mlieBracket I (X - X') Y) W x := by
              simp [CovariantDerivative.curvatureAux]
    _ = (cov.along X (cov.along Y W) x - cov.along X' (cov.along Y W) x) -
          (cov.along Y (cov.along X W) x - cov.along Y (cov.along X' W) x) -
          (cov.along (VectorField.mlieBracket I X Y) W x -
            cov.along (VectorField.mlieBracket I X' Y) W x) := by
              rw [h1, h2, h3]
    _ = (cov.along X (cov.along Y W) x - cov.along Y (cov.along X W) x -
          cov.along (VectorField.mlieBracket I X Y) W x) -
        (cov.along X' (cov.along Y W) x - cov.along Y (cov.along X' W) x -
          cov.along (VectorField.mlieBracket I X' Y) W x) := by
            abel_nf
    _ = cov.curvatureAux X Y W x - cov.curvatureAux X' Y W x := by
          simp [CovariantDerivative.curvatureAux]

private lemma along_curvatureAux_sub_curvatureAux_along_apply
    {X Y Z W : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (fun y ↦ TotalSpace.mk' E y (W y))) :
    cov.along X (cov.curvatureAux Y Z W) x -
        cov.curvatureAux Y Z (cov.along X W) x =
      cov.along X (cov.along Y (cov.along Z W)) x -
        cov.along X (cov.along Z (cov.along Y W)) x -
        cov.along Y (cov.along Z (cov.along X W)) x +
        cov.along Z (cov.along Y (cov.along X W)) x +
        -cov.curvatureAux X (VectorField.mlieBracket I Y Z) W x -
        cov.along (VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z)) W x := by
  have hX₁ := hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hY₁ := hY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hZ₁ := hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hW₂ := hW.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hAlongZW₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (cov.along Z W y)) :=
    cov.contMDiff_along (n := 2) hZ hW
  have hAlongYW₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (cov.along Y W y)) :=
    cov.contMDiff_along (n := 2) hY hW
  have hAlongXW₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (cov.along X W y)) :=
    cov.contMDiff_along (n := 2) hX hW
  have hYAlongZW₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along Y (cov.along Z W) y)) :=
    cov.contMDiff_along (n := 1) hY₁ hAlongZW₂
  have hZAlongYW₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along Z (cov.along Y W) y)) :=
    cov.contMDiff_along (n := 1) hZ₁ hAlongYW₂
  have hBracketYZ₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (VectorField.mlieBracket I Y Z y)) := by
    simpa using
      (ContDiff.mlieBracket_vectorField (I := I) (m := (1 : ℕ∞)) (n := (2 : ℕ∞))
        hY hZ (by norm_num))
  have hBracketYZW₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y
          (cov.along (VectorField.mlieBracket I Y Z) W y)) :=
    cov.contMDiff_along (n := 1) hBracketYZ₁ hW₂
  have hA : MDiffAt (T% (cov.along Y (cov.along Z W))) x :=
    (hYAlongZW₁ x).mdifferentiableAt one_ne_zero
  have hB : MDiffAt (T% (cov.along Z (cov.along Y W))) x :=
    (hZAlongYW₁ x).mdifferentiableAt one_ne_zero
  have hC : MDiffAt (T% (cov.along (VectorField.mlieBracket I Y Z) W)) x :=
    (hBracketYZW₁ x).mdifferentiableAt one_ne_zero
  have hBplusC :
      MDiffAt (T% (cov.along Z (cov.along Y W) +
        cov.along (VectorField.mlieBracket I Y Z) W)) x :=
    mdifferentiableAt_add_section hB hC
  have hCurvYZ :
      cov.curvatureAux Y Z W =
        cov.along Y (cov.along Z W) -
          (cov.along Z (cov.along Y W) +
            cov.along (VectorField.mlieBracket I Y Z) W) := by
    ext y
    simp [CovariantDerivative.curvatureAux]
    abel_nf
  calc
    cov.along X (cov.curvatureAux Y Z W) x -
        cov.curvatureAux Y Z (cov.along X W) x
      = (cov.along X (cov.along Y (cov.along Z W)) x -
            (cov.along X (cov.along Z (cov.along Y W)) x +
              cov.along X (cov.along (VectorField.mlieBracket I Y Z) W) x)) -
          (cov.along Y (cov.along Z (cov.along X W)) x -
            cov.along Z (cov.along Y (cov.along X W)) x -
            cov.along (VectorField.mlieBracket I Y Z) (cov.along X W) x) := by
              rw [hCurvYZ, cov.along_sub_right_apply hA hBplusC,
                cov.along_add_right_apply hB hC]
              simp [CovariantDerivative.curvatureAux]
    _ = cov.along X (cov.along Y (cov.along Z W)) x -
          cov.along X (cov.along Z (cov.along Y W)) x -
          cov.along Y (cov.along Z (cov.along X W)) x +
          cov.along Z (cov.along Y (cov.along X W)) x -
          cov.along X (cov.along (VectorField.mlieBracket I Y Z) W) x +
          cov.along (VectorField.mlieBracket I Y Z) (cov.along X W) x := by
            abel_nf
    _ = cov.along X (cov.along Y (cov.along Z W)) x -
          cov.along X (cov.along Z (cov.along Y W)) x -
          cov.along Y (cov.along Z (cov.along X W)) x +
          cov.along Z (cov.along Y (cov.along X W)) x +
          -cov.curvatureAux X (VectorField.mlieBracket I Y Z) W x -
          cov.along (VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z)) W x := by
            simp [CovariantDerivative.curvatureAux]
            abel_nf

/-! The commutator expansion above is also useful outside the proof of the
cyclic second Bianchi identity.  Keep the exact bracket correction public so
curvature-evolution developments can use it without duplicating the nested
covariant-derivative calculation. -/

/-- The commutator of a covariant derivative with the curvature commutator,
with all Lie-bracket correction terms displayed explicitly.  This is the
actual local second-derivative identity proved from the covariant-derivative
laws; no normal-frame or coordinate assumption is part of the statement. -/
theorem curvatureAux_covariantDerivative_commutator_apply
    {X Y Z W : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (fun y ↦ TotalSpace.mk' E y (W y))) :
    cov.along X (cov.curvatureAux Y Z W) x -
        cov.curvatureAux Y Z (cov.along X W) x =
      cov.along X (cov.along Y (cov.along Z W)) x -
        cov.along X (cov.along Z (cov.along Y W)) x -
        cov.along Y (cov.along Z (cov.along X W)) x +
        cov.along Z (cov.along Y (cov.along X W)) x +
        -cov.curvatureAux X (VectorField.mlieBracket I Y Z) W x -
        cov.along (VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z)) W x := by
  exact cov.along_curvatureAux_sub_curvatureAux_along_apply hX hY hZ hW

private lemma cyclic_along_curvatureAux_sub_curvatureAux_along_apply
    {X Y Z W : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (fun y ↦ TotalSpace.mk' E y (W y))) :
    (cov.along X (cov.curvatureAux Y Z W) x - cov.curvatureAux Y Z (cov.along X W) x) +
      (cov.along Y (cov.curvatureAux Z X W) x - cov.curvatureAux Z X (cov.along Y W) x) +
      (cov.along Z (cov.curvatureAux X Y W) x - cov.curvatureAux X Y (cov.along Z W) x) =
      cov.curvatureAux (VectorField.mlieBracket I X Y) Z W x +
        cov.curvatureAux (VectorField.mlieBracket I Y Z) X W x +
        cov.curvatureAux (VectorField.mlieBracket I Z X) Y W x := by
  have hXYZ := cov.along_curvatureAux_sub_curvatureAux_along_apply (x := x) hX hY hZ hW
  have hYZX := cov.along_curvatureAux_sub_curvatureAux_along_apply (x := x) hY hZ hX hW
  have hZXY := cov.along_curvatureAux_sub_curvatureAux_along_apply (x := x) hZ hX hY hW
  have hSwap₁ :
      -cov.curvatureAux X (VectorField.mlieBracket I Y Z) W x =
        cov.curvatureAux (VectorField.mlieBracket I Y Z) X W x := by
    have h' :
        cov.curvatureAux X (VectorField.mlieBracket I Y Z) W x =
          -cov.curvatureAux (VectorField.mlieBracket I Y Z) X W x := by
      simpa [Pi.neg_apply] using congrArg (fun s => s x) <|
        cov.curvatureAux_swap (X := X) (Y := VectorField.mlieBracket I Y Z) (σ := W)
    calc
      -cov.curvatureAux X (VectorField.mlieBracket I Y Z) W x =
          -(-cov.curvatureAux (VectorField.mlieBracket I Y Z) X W x) := by rw [h']
      _ = cov.curvatureAux (VectorField.mlieBracket I Y Z) X W x := by simp
  have hSwap₂ :
      -cov.curvatureAux Y (VectorField.mlieBracket I Z X) W x =
        cov.curvatureAux (VectorField.mlieBracket I Z X) Y W x := by
    have h' :
        cov.curvatureAux Y (VectorField.mlieBracket I Z X) W x =
          -cov.curvatureAux (VectorField.mlieBracket I Z X) Y W x := by
      simpa [Pi.neg_apply] using congrArg (fun s => s x) <|
        cov.curvatureAux_swap (X := Y) (Y := VectorField.mlieBracket I Z X) (σ := W)
    calc
      -cov.curvatureAux Y (VectorField.mlieBracket I Z X) W x =
          -(-cov.curvatureAux (VectorField.mlieBracket I Z X) Y W x) := by rw [h']
      _ = cov.curvatureAux (VectorField.mlieBracket I Z X) Y W x := by simp
  have hSwap₃ :
      -cov.curvatureAux Z (VectorField.mlieBracket I X Y) W x =
        cov.curvatureAux (VectorField.mlieBracket I X Y) Z W x := by
    have h' :
        cov.curvatureAux Z (VectorField.mlieBracket I X Y) W x =
          -cov.curvatureAux (VectorField.mlieBracket I X Y) Z W x := by
      simpa [Pi.neg_apply] using congrArg (fun s => s x) <|
        cov.curvatureAux_swap (X := Z) (Y := VectorField.mlieBracket I X Y) (σ := W)
    calc
      -cov.curvatureAux Z (VectorField.mlieBracket I X Y) W x =
          -(-cov.curvatureAux (VectorField.mlieBracket I X Y) Z W x) := by rw [h']
      _ = cov.curvatureAux (VectorField.mlieBracket I X Y) Z W x := by simp
  have hJac := cyclic_mlieBracket_apply_eq_zero (I := I) (x := x) hX hY hZ
  have hNested :
      cov.along (VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z)) W x +
        cov.along (VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X)) W x +
        cov.along (VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y)) W x = 0 := by
    calc
      cov.along (VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z)) W x +
          cov.along (VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X)) W x +
          cov.along (VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y)) W x
        = cov W x
            (VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x +
              VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x +
              VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x) := by
                simp [CovariantDerivative.along, map_add]
      _ = 0 := by simp [hJac]
  calc
    (cov.along X (cov.curvatureAux Y Z W) x - cov.curvatureAux Y Z (cov.along X W) x) +
        (cov.along Y (cov.curvatureAux Z X W) x - cov.curvatureAux Z X (cov.along Y W) x) +
        (cov.along Z (cov.curvatureAux X Y W) x - cov.curvatureAux X Y (cov.along Z W) x)
      = (-cov.curvatureAux X (VectorField.mlieBracket I Y Z) W x -
            cov.along (VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z)) W x) +
          (-cov.curvatureAux Y (VectorField.mlieBracket I Z X) W x -
            cov.along (VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X)) W x) +
          (-cov.curvatureAux Z (VectorField.mlieBracket I X Y) W x -
            cov.along (VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y)) W x) := by
              rw [hXYZ, hYZX, hZXY]
              abel_nf
    _ = (cov.curvatureAux (VectorField.mlieBracket I Y Z) X W x +
            cov.curvatureAux (VectorField.mlieBracket I Z X) Y W x +
            cov.curvatureAux (VectorField.mlieBracket I X Y) Z W x) -
          (cov.along (VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z)) W x +
            cov.along (VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X)) W x +
            cov.along (VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y)) W x) := by
              rw [hSwap₁, hSwap₂, hSwap₃]
              abel_nf
    _ = cov.curvatureAux (VectorField.mlieBracket I X Y) Z W x +
          cov.curvatureAux (VectorField.mlieBracket I Y Z) X W x +
          cov.curvatureAux (VectorField.mlieBracket I Z X) Y W x := by
            rw [hNested]
            abel_nf

private lemma cyclic_curvatureAux_along_apply_eq_curvatureAux_bracket_apply_of_torsion_eq_zero
    (hT : cov.torsion = 0)
    {X Y Z W : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (fun y ↦ TotalSpace.mk' E y (W y))) :
    cov.curvatureAux (cov.along X Y) Z W x +
      cov.curvatureAux Y (cov.along X Z) W x +
      cov.curvatureAux (cov.along Y Z) X W x +
      cov.curvatureAux Z (cov.along Y X) W x +
      cov.curvatureAux (cov.along Z X) Y W x +
      cov.curvatureAux X (cov.along Z Y) W x =
      cov.curvatureAux (VectorField.mlieBracket I X Y) Z W x +
        cov.curvatureAux (VectorField.mlieBracket I Y Z) X W x +
        cov.curvatureAux (VectorField.mlieBracket I Z X) Y W x := by
  have hX₁ := hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hY₁ := hY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hZ₁ := hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hW₂ := hW.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hXY₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along X Y y)) :=
    cov.contMDiff_along (n := 1) hX₁ hY
  have hYX₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along Y X y)) :=
    cov.contMDiff_along (n := 1) hY₁ hX
  have hYZ₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along Y Z y)) :=
    cov.contMDiff_along (n := 1) hY₁ hZ
  have hZY₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along Z Y y)) :=
    cov.contMDiff_along (n := 1) hZ₁ hY
  have hZX₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along Z X y)) :=
    cov.contMDiff_along (n := 1) hZ₁ hX
  have hXZ₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (cov.along X Z y)) :=
    cov.contMDiff_along (n := 1) hX₁ hZ
  have hXY := cov.along_sub_eq_mlieBracket_of_torsion_eq_zero hT hX₁ hY₁
  have hYZ := cov.along_sub_eq_mlieBracket_of_torsion_eq_zero hT hY₁ hZ₁
  have hZX := cov.along_sub_eq_mlieBracket_of_torsion_eq_zero hT hZ₁ hX₁
  have hPairXY :
      cov.curvatureAux (cov.along X Y) Z W x -
        cov.curvatureAux (cov.along Y X) Z W x =
      cov.curvatureAux (VectorField.mlieBracket I X Y) Z W x := by
    calc
      cov.curvatureAux (cov.along X Y) Z W x -
          cov.curvatureAux (cov.along Y X) Z W x
        = cov.curvatureAux (cov.along X Y - cov.along Y X) Z W x := by
            symm
            exact cov.curvatureAux_sub_left_apply (x := x) hXY₁ hYX₁ hW₂
      _ = cov.curvatureAux (VectorField.mlieBracket I X Y) Z W x := by rw [hXY]
  have hPairYZ :
      cov.curvatureAux (cov.along Y Z) X W x -
        cov.curvatureAux (cov.along Z Y) X W x =
      cov.curvatureAux (VectorField.mlieBracket I Y Z) X W x := by
    calc
      cov.curvatureAux (cov.along Y Z) X W x -
          cov.curvatureAux (cov.along Z Y) X W x
        = cov.curvatureAux (cov.along Y Z - cov.along Z Y) X W x := by
            symm
            exact cov.curvatureAux_sub_left_apply (x := x) hYZ₁ hZY₁ hW₂
      _ = cov.curvatureAux (VectorField.mlieBracket I Y Z) X W x := by rw [hYZ]
  have hPairZX :
      cov.curvatureAux (cov.along Z X) Y W x -
        cov.curvatureAux (cov.along X Z) Y W x =
      cov.curvatureAux (VectorField.mlieBracket I Z X) Y W x := by
    calc
      cov.curvatureAux (cov.along Z X) Y W x -
          cov.curvatureAux (cov.along X Z) Y W x
        = cov.curvatureAux (cov.along Z X - cov.along X Z) Y W x := by
            symm
            exact cov.curvatureAux_sub_left_apply (x := x) hZX₁ hXZ₁ hW₂
      _ = cov.curvatureAux (VectorField.mlieBracket I Z X) Y W x := by rw [hZX]
  have hSwap₁ :
      cov.curvatureAux Y (cov.along X Z) W x =
        -cov.curvatureAux (cov.along X Z) Y W x := by
    simpa using congrArg (fun s => s x) <|
      cov.curvatureAux_swap (X := Y) (Y := cov.along X Z) (σ := W)
  have hSwap₂ :
      cov.curvatureAux Z (cov.along Y X) W x =
        -cov.curvatureAux (cov.along Y X) Z W x := by
    simpa using congrArg (fun s => s x) <|
      cov.curvatureAux_swap (X := Z) (Y := cov.along Y X) (σ := W)
  have hSwap₃ :
      cov.curvatureAux X (cov.along Z Y) W x =
        -cov.curvatureAux (cov.along Z Y) X W x := by
    simpa using congrArg (fun s => s x) <|
      cov.curvatureAux_swap (X := X) (Y := cov.along Z Y) (σ := W)
  calc
    cov.curvatureAux (cov.along X Y) Z W x +
        cov.curvatureAux Y (cov.along X Z) W x +
        cov.curvatureAux (cov.along Y Z) X W x +
        cov.curvatureAux Z (cov.along Y X) W x +
        cov.curvatureAux (cov.along Z X) Y W x +
        cov.curvatureAux X (cov.along Z Y) W x
      = (cov.curvatureAux (cov.along X Y) Z W x -
            cov.curvatureAux (cov.along Y X) Z W x) +
          (cov.curvatureAux (cov.along Y Z) X W x -
            cov.curvatureAux (cov.along Z Y) X W x) +
          (cov.curvatureAux (cov.along Z X) Y W x -
            cov.curvatureAux (cov.along X Z) Y W x) := by
              rw [hSwap₁, hSwap₂, hSwap₃]
              abel_nf
    _ = cov.curvatureAux (VectorField.mlieBracket I X Y) Z W x +
          cov.curvatureAux (VectorField.mlieBracket I Y Z) X W x +
          cov.curvatureAux (VectorField.mlieBracket I Z X) Y W x := by
            rw [hPairXY, hPairYZ, hPairZX]

theorem secondBianchiAux_apply_of_torsion_eq_zero
    (hT : cov.torsion = 0)
    {X Y Z W : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (fun y ↦ TotalSpace.mk' E y (W y))) :
    cov.secondBianchiAux X Y Z W x +
      cov.secondBianchiAux Y Z X W x +
      cov.secondBianchiAux Z X Y W x = 0 := by
  have hComm :=
    cov.cyclic_along_curvatureAux_sub_curvatureAux_along_apply (x := x) hX hY hZ hW
  have hDeriv :=
    cov.cyclic_curvatureAux_along_apply_eq_curvatureAux_bracket_apply_of_torsion_eq_zero
      (x := x) hT hX hY hZ hW
  calc
    cov.secondBianchiAux X Y Z W x +
        cov.secondBianchiAux Y Z X W x +
        cov.secondBianchiAux Z X Y W x
      = (cov.along X (cov.curvatureAux Y Z W) x - cov.curvatureAux Y Z (cov.along X W) x) +
          (cov.along Y (cov.curvatureAux Z X W) x - cov.curvatureAux Z X (cov.along Y W) x) +
          (cov.along Z (cov.curvatureAux X Y W) x - cov.curvatureAux X Y (cov.along Z W) x) -
          (cov.curvatureAux (cov.along X Y) Z W x +
            cov.curvatureAux Y (cov.along X Z) W x +
            cov.curvatureAux (cov.along Y Z) X W x +
            cov.curvatureAux Z (cov.along Y X) W x +
            cov.curvatureAux (cov.along Z X) Y W x +
            cov.curvatureAux X (cov.along Z Y) W x) := by
              simp [CovariantDerivative.secondBianchiAux]
              abel_nf
    _ = 0 := by
      rw [hComm, hDeriv]
      abel_nf

theorem secondBianchiAux_of_torsion_eq_zero
    (hT : cov.torsion = 0)
    {X Y Z W : Π x : M, TM x}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (fun y ↦ TotalSpace.mk' E y (W y))) :
    cov.secondBianchiAux X Y Z W +
      cov.secondBianchiAux Y Z X W +
      cov.secondBianchiAux Z X Y W = 0 := by
  ext x
  exact cov.secondBianchiAux_apply_of_torsion_eq_zero hT hX hY hZ hW

end SecondBianchi

end CovariantDerivative
