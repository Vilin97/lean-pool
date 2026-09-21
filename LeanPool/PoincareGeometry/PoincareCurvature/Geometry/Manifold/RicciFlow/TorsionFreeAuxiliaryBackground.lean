/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TorsionRegularity

/-!
# A fixed smooth torsion-free auxiliary background

On a smooth manifold, this module selects a global `C²` torsion-free affine
connection from a `C²` Riemannian tangent-bundle structure together with a
`C³` tangent vector-bundle structure.  Its constant connection family is the
background used by the standard Ricci--DeTurck principal-part calculation and
by the auxiliary tensor-heat construction.  It is deliberately not claimed to
be the Levi--Civita connection of the initial metric: the point is to supply a
torsion-free background with the regularity required by those analytic
constructions.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- A fixed `C²` torsion-free affine tangent connection. -/
structure FixedTorsionFreeAffineBackground where
  /-- The selected connection. -/
  covariantDerivative : CovariantDerivative I E TM
  /-- The connection has zero torsion. -/
  isTorsionFree : covariantDerivative.IsTorsionFree
  /-- The spatial regularity used by the tensor-heat construction. -/
  contMDiff : CovariantDerivative.ContMDiffCovariantDerivative covariantDerivative 2

/-- Every sigma-compact smooth manifold satisfying the displayed `C²`
Riemannian-bundle and `C³` tangent-vector-bundle hypotheses admits a fixed
`C²` torsion-free affine background. -/
theorem fixedTorsionFreeAffineBackground_nonempty
    [SigmaCompactSpace M] :
    Nonempty (FixedTorsionFreeAffineBackground (I := I) (M := M)) := by
  rcases CovariantDerivative.exists_contMDiffTorsionFreeAffineConnection_two
    (I := I) (E := E) (M := M) with ⟨cov, hTorsionFree, hcov⟩
  exact ⟨⟨cov, hTorsionFree, hcov⟩⟩

/-- A chosen fixed `C²` torsion-free affine background. -/
noncomputable def fixedTorsionFreeAffineBackground
    [SigmaCompactSpace M] :
    FixedTorsionFreeAffineBackground (I := I) (M := M) :=
  Classical.choice (fixedTorsionFreeAffineBackground_nonempty (I := I) (M := M))

/-- A fixed auxiliary connection viewed as the constant family used by
Ricci--DeTurck flow. -/
def FixedTorsionFreeAffineBackground.constantConnection
    (background : FixedTorsionFreeAffineBackground (I := I) (M := M)) :
    ConnectionFamily (I := I) (M := M) :=
  CovariantDerivative.TimeDependentCovariantDerivative.const
    (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)
    background.covariantDerivative

@[simp] theorem FixedTorsionFreeAffineBackground.constantConnection_apply
    (background : FixedTorsionFreeAffineBackground (I := I) (M := M)) (t : ℝ) :
    background.constantConnection t = background.covariantDerivative :=
  rfl

/-- Each slice of the constant background remains `C²`. -/
theorem FixedTorsionFreeAffineBackground.constantConnection_contMDiff_two
    (background : FixedTorsionFreeAffineBackground (I := I) (M := M)) :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (background.constantConnection t) 2 := by
  intro t
  simpa only [FixedTorsionFreeAffineBackground.constantConnection_apply] using
    background.contMDiff

/-- Each slice of the constant background has the `C¹` regularity consumed by
the geometric Ricci--DeTurck assembly. -/
theorem FixedTorsionFreeAffineBackground.constantConnection_contMDiff_one
    (background : FixedTorsionFreeAffineBackground (I := I) (M := M)) :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (background.constantConnection t) 1 := by
  intro t
  letI : CovariantDerivative.ContMDiffCovariantDerivative
      background.covariantDerivative 2 := background.contMDiff
  simpa only [FixedTorsionFreeAffineBackground.constantConnection_apply] using
    (CovariantDerivative.contMDiffCovariantDerivative_one_of_contMDiffCovariantDerivative_two
      (I := I) (F := E) (V := TM))

/-- Each slice of the constant background is torsion-free. -/
theorem FixedTorsionFreeAffineBackground.constantConnection_isTorsionFree
    (background : FixedTorsionFreeAffineBackground (I := I) (M := M)) :
    ∀ t : ℝ, (background.constantConnection t).IsTorsionFree := by
  intro t
  simpa only [FixedTorsionFreeAffineBackground.constantConnection_apply] using
    background.isTorsionFree

/-- The zero-torsion form of the fixed-background fact, matching the
connection-change and Ricci--DeTurck assembly hypotheses. -/
theorem FixedTorsionFreeAffineBackground.constantConnection_torsion_eq_zero
    (background : FixedTorsionFreeAffineBackground (I := I) (M := M)) :
    ∀ t : ℝ, (background.constantConnection t).torsion = 0 :=
  background.constantConnection_isTorsionFree

/-- The canonical chosen background supplies `C²` slice regularity. -/
theorem fixedTorsionFreeAffineBackground_constantConnection_contMDiff_two
    [SigmaCompactSpace M] :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        ((fixedTorsionFreeAffineBackground (I := I) (M := M)).constantConnection t) 2 :=
  (fixedTorsionFreeAffineBackground (I := I) (M := M)).constantConnection_contMDiff_two

/-- The canonical chosen background supplies the `C¹` slice regularity used
by the Ricci--DeTurck geometry. -/
theorem fixedTorsionFreeAffineBackground_constantConnection_contMDiff_one
    [SigmaCompactSpace M] :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        ((fixedTorsionFreeAffineBackground (I := I) (M := M)).constantConnection t) 1 :=
  (fixedTorsionFreeAffineBackground (I := I) (M := M)).constantConnection_contMDiff_one

/-- The canonical chosen background is torsion-free at every time. -/
theorem fixedTorsionFreeAffineBackground_constantConnection_isTorsionFree
    [SigmaCompactSpace M] :
    ∀ t : ℝ,
      ((fixedTorsionFreeAffineBackground (I := I) (M := M)).constantConnection t).IsTorsionFree :=
  (fixedTorsionFreeAffineBackground (I := I) (M := M)).constantConnection_isTorsionFree

/-- The canonical chosen background has zero torsion at every time. -/
theorem fixedTorsionFreeAffineBackground_constantConnection_torsion_eq_zero
    [SigmaCompactSpace M] :
    ∀ t : ℝ,
      ((fixedTorsionFreeAffineBackground (I := I) (M := M)).constantConnection t).torsion = 0 :=
  (fixedTorsionFreeAffineBackground (I := I) (M := M)).constantConnection_torsion_eq_zero

end RicciFlow
