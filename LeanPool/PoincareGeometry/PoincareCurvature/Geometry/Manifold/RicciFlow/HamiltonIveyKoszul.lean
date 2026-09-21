/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi

/-!
# Koszul identity for the Hamilton--Ivey development

This file derives the pointwise Koszul identity from the repository's actual
torsion-free and metric-compatible predicates. It is a static geometric
bridge for the later metric-to-connection variation argument; no time
regularity or evolution identity is assumed here.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The classical Koszul formula for an actual torsion-free, metric-compatible
connection on the tangent bundle. Directional derivatives are the manifold
mvfderiv, and the brackets are the manifold Lie brackets. -/
theorem koszul_formula
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative cov 1]
    (hLevi : cov.IsLeviCivita)
    {X Y Z : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Z y))) :
    2 * ⟪cov.along X Y x, Z x⟫ =
      mvfderiv (I := I) (fun y ↦ ⟪Y y, Z y⟫) x (X x) +
      mvfderiv (I := I) (fun y ↦ ⟪X y, Z y⟫) x (Y x) -
      mvfderiv (I := I) (fun y ↦ ⟪X y, Y y⟫) x (Z x) -
      ⟪X x, VectorField.mlieBracket I Y Z x⟫ +
      ⟪Y x, VectorField.mlieBracket I Z X x⟫ +
      ⟪Z x, VectorField.mlieBracket I X Y x⟫ := by
  have hXmd (y : M) : MDiffAt (T% X) y :=
    (hX y).mdifferentiableAt (by norm_num)
  have hYmd (y : M) : MDiffAt (T% Y) y :=
    (hY y).mdifferentiableAt (by norm_num)
  have hZmd (y : M) : MDiffAt (T% Z) y :=
    (hZ y).mdifferentiableAt (by norm_num)
  have hmetric₁ :
      mvfderiv (I := I) (fun y ↦ ⟪Y y, Z y⟫) x (X x) =
        ⟪cov.along X Y x, Z x⟫ + ⟪Y x, cov.along X Z x⟫ := by
    simpa [CovariantDerivative.along] using hLevi.2 (hYmd x) (hZmd x) (X x)
  have hmetric₂ :
      mvfderiv (I := I) (fun y ↦ ⟪X y, Z y⟫) x (Y x) =
        ⟪cov.along Y X x, Z x⟫ + ⟪X x, cov.along Y Z x⟫ := by
    simpa [CovariantDerivative.along] using hLevi.2 (hXmd x) (hZmd x) (Y x)
  have hmetric₃ :
      mvfderiv (I := I) (fun y ↦ ⟪X y, Y y⟫) x (Z x) =
        ⟪cov.along Z X x, Y x⟫ + ⟪X x, cov.along Z Y x⟫ := by
    simpa [CovariantDerivative.along] using hLevi.2 (hXmd x) (hYmd x) (Z x)
  have htorsionXY :=
    along_sub_eq_mlieBracket_of_torsion_eq_zero (cov := cov) hLevi.1 hX hY
  have htorsionYZ :=
    along_sub_eq_mlieBracket_of_torsion_eq_zero (cov := cov) hLevi.1 hY hZ
  have htorsionZX :=
    along_sub_eq_mlieBracket_of_torsion_eq_zero (cov := cov) hLevi.1 hZ hX
  have hYX : cov.along Y X x =
      cov.along X Y x - VectorField.mlieBracket I X Y x := by
    have h : cov.along X Y x - cov.along Y X x =
        VectorField.mlieBracket I X Y x := by
      simpa using congrFun htorsionXY x
    rw [← h]
    abel
  have hYZ : cov.along Y Z x =
      cov.along Z Y x + VectorField.mlieBracket I Y Z x := by
    have h : cov.along Y Z x - cov.along Z Y x =
        VectorField.mlieBracket I Y Z x := by
      simpa using congrFun htorsionYZ x
    rw [← h]
    abel
  have hZX : cov.along Z X x =
      cov.along X Z x + VectorField.mlieBracket I Z X x := by
    have h : cov.along Z X x - cov.along X Z x =
        VectorField.mlieBracket I Z X x := by
      simpa using congrFun htorsionZX x
    rw [← h]
    abel
  have hmetric₂' :
      mvfderiv (I := I) (fun y ↦ ⟪X y, Z y⟫) x (Y x) =
        ⟪cov.along X Y x, Z x⟫ - ⟪VectorField.mlieBracket I X Y x, Z x⟫ +
          ⟪cov.along Z Y x, X x⟫ + ⟪VectorField.mlieBracket I Y Z x, X x⟫ := by
    calc
      _ = ⟪cov.along Y X x, Z x⟫ + ⟪X x, cov.along Y Z x⟫ := hmetric₂
      _ = ⟪cov.along X Y x - VectorField.mlieBracket I X Y x, Z x⟫ +
          ⟪X x, cov.along Z Y x + VectorField.mlieBracket I Y Z x⟫ := by
            rw [hYX, hYZ]
      _ = _ := by
        simp [inner_sub_left, inner_add_right, real_inner_comm]
        abel
  have hmetric₃' :
      mvfderiv (I := I) (fun y ↦ ⟪X y, Y y⟫) x (Z x) =
        ⟪cov.along X Z x, Y x⟫ + ⟪VectorField.mlieBracket I Z X x, Y x⟫ +
          ⟪cov.along Z Y x, X x⟫ := by
    calc
      _ = ⟪cov.along Z X x, Y x⟫ + ⟪X x, cov.along Z Y x⟫ := hmetric₃
      _ = ⟪cov.along X Z x + VectorField.mlieBracket I Z X x, Y x⟫ +
          ⟪X x, cov.along Z Y x⟫ := by rw [hZX]
      _ = _ := by simp [inner_add_left, real_inner_comm]
  rw [hmetric₁, hmetric₂', hmetric₃']
  rw [real_inner_comm (Y x) (cov.along X Z x),
    real_inner_comm (X x) (cov.along Z Y x),
    real_inner_comm (X x) (VectorField.mlieBracket I Y Z x),
    real_inner_comm (Z x) (VectorField.mlieBracket I X Y x),
    real_inner_comm (Y x) (VectorField.mlieBracket I Z X x)]
  ring

end CovariantDerivative
