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

public import LeanPool.PoincareGeometry.AlmostSchur.MetricTorsionCorrection
public import LeanPool.PoincareGeometry.AlmostSchur.MetricConnectionCoordinates
public import LeanPool.PoincareGeometry.AlmostSchur.TorsionCoordinates

/-! # Correcting an actual connection to a Levi–Civita connection

The correction uses mathlib's actual metric-defect and torsion tensors.
No existence or regularity of a seed connection is asserted in this module.
-/

@[expose] public noncomputable section
open Bundle FiberBundle VectorField
open scoped Manifold ContDiff
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)
local instance leviCivitaCorrectionFiniteTangent (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- The actual metric defect is symmetric in its two metric slots. -/
theorem derivMetricTensor_symmetric (cov : CovariantDerivative I E TM)
    (x : M) (u v w : TM x) :
    cov.derivMetricTensor x u v w = cov.derivMetricTensor x v u w := by
  rw [cov.derivMetricTensor_apply_eq_extend w u v,
    cov.derivMetricTensor_apply_eq_extend w v u]
  have he : (fun y ↦ inner ℝ (FiberBundle.extend E u y) (FiberBundle.extend E v y)) =
      (fun y ↦ inner ℝ (FiberBundle.extend E v y) (FiberBundle.extend E u y)) := by
    funext y
    exact real_inner_comm _ _
  rw [he]
  rw [real_inner_comm (cov (FiberBundle.extend E u) x w) v,
    real_inner_comm u (cov (FiberBundle.extend E v) x w)]
  ring

/-- A concrete correction of a seed connection. Direction comes first in the
Koszul correction, whereas `addOneForm` takes the section value first. -/
def leviCivitaCorrected (cov : CovariantDerivative I E TM) : CovariantDerivative I E TM :=
  cov.addOneForm (fun x ↦ (koszulCorrection (cov.derivMetricTensor x) (cov.torsion x)).flip)

/-- Evaluation of the actual corrected connection on any section. -/
theorem leviCivitaCorrected_apply (cov : CovariantDerivative I E TM)
    (Z : Π x, TM x) (x : M) (u : TM x) :
    leviCivitaCorrected cov Z x u = cov Z x u +
      koszulCorrection (cov.derivMetricTensor x) (cov.torsion x) u (Z x) := rfl

/-- The constructed corrected connection is compatible with the actual metric. -/
theorem leviCivitaCorrected_metricCompatible (cov : CovariantDerivative I E TM) :
    tangentMetricCompatible (leviCivitaCorrected cov) := by
  apply (CovariantDerivative.isMetricCompatible_iff _).mpr
  intro x X Z W _ hZ hW
  have hd : cov.derivMetricTensor x (Z x) (W x) (X x) =
      mvfderiv I (fun y ↦ inner ℝ (Z y) (W y)) x (X x) -
        inner ℝ (cov Z x (X x)) (W x) - inner ℝ (Z x) (cov W x (X x)) := by
    exact @CovariantDerivative.derivMetricTensor_apply E _ _ H _ I M _ _ E _ _ TM _
      (fun y ↦ inferInstance) (fun y ↦ inferInstance) _ Z W cov _ _ X _ _ x hZ hW
  have hc := koszulCorrection_metric (cov.derivMetricTensor x) (cov.torsion x)
    (derivMetricTensor_symmetric cov x) (cov.torsion_antisymm) (X x) (Z x) (W x)
  simp only [leviCivitaCorrected_apply, inner_add_left, inner_add_right]
  linarith

/-- The constructed corrected connection has zero actual torsion tensor. -/
theorem leviCivitaCorrected_torsion (cov : CovariantDerivative I E TM) :
    (leviCivitaCorrected cov).torsion = 0 := by
  apply (leviCivitaCorrected cov).torsion_eq_zero_iff.mpr
  intro X Y x hX hY
  have ht := cov.torsion_apply hX hY
  have hc := koszulCorrection_torsion (cov.derivMetricTensor x) (cov.torsion x)
    (derivMetricTensor_symmetric cov x) (cov.torsion_antisymm) (X x) (Y x)
  simp only [leviCivitaCorrected_apply]
  calc
    _ = (cov Y x (X x) - cov X x (Y x)) +
        (koszulCorrection (cov.derivMetricTensor x) (cov.torsion x) (X x) (Y x) -
          koszulCorrection (cov.derivMetricTensor x) (cov.torsion x) (Y x) (X x)) := by abel
    _ = _ := by rw [hc, ht]; abel

end AlmostSchur
