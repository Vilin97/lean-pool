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

public import LeanPool.PoincareGeometry.AlmostSchur.ThirdHessianCommutator
public import LeanPool.PoincareGeometry.AlmostSchur.HessianSymmetry

/-! # Symmetry in the last two slots of the corrected third Hessian

The scalar functions being differentiated are equal by the proved Hessian
symmetry. Both covariant slot corrections are then exchanged explicitly.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff
namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)

/-- Last-slot symmetry follows by differentiating the genuine Hessian symmetry,
not by treating a moving frame as parallel. C² suffices for this equality;
the C³ commutator theorem supplies the subsequent regularity interpretation. -/
theorem thirdHessian_symmetric_last (cov : CovariantDerivative I E TM)
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (X Y W : Π x, TM x) (x : M) :
    thirdHessian cov f X Y W x = thirdHessian cov f X W Y x := by
  have he : (fun y ↦ hessian cov f y (Y y) (W y)) =
      (fun y ↦ hessian cov f y (W y) (Y y)) := by
    funext y
    exact hessian_symmetric cov hm ht hf y _ _
  unfold thirdHessian
  rw [he, hessian_symmetric cov hm ht hf x (covariantAlong cov X Y x) (W x),
    hessian_symmetric cov hm ht hf x (Y x) (covariantAlong cov X W x)]
  ring

end AlmostSchur
