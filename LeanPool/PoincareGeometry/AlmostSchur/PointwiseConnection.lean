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

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Tactic

/-! # An explicit seed connection from pointwise tangent charts

At each evaluation point, differentiate the section in the tangent
trivialization centered at that point. The connection laws hold pointwise.
The point-dependent chart selection does NOT imply any global regularity;
this construction is only a seed for the metric/torsion correction.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff Topology
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
local notation "TM" => (TangentSpace I : M → Type _)

/-- Coordinates of an actual tangent section in a fixed tangent trivialization. -/
def tangentSectionCoordinates (c : M) (Z : Π y, TM y) (y : M) : E :=
  (trivializationAt E TM c).continuousLinearMapAt ℝ y (Z y)

/-- A differentiable section has differentiable coordinates in any chart
whose base contains the evaluation point. -/
theorem mdifferentiableAt_tangentSectionCoordinates (c : M) {Z : Π y, TM y} {x : M}
    (hx : x ∈ (trivializationAt E TM c).baseSet) (hZ : MDiffAt (T% Z) x) :
    MDifferentiableAt I 𝓘(ℝ, E) (tangentSectionCoordinates c Z) x := by
  let e := trivializationAt E TM c
  have h := (e.mdifferentiableAt_section_iff I Z hx).mp hZ
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact e.continuousLinearMapAt_apply_of_mem ℝ hy (Z y)

/-- A concrete global connection. Regularity is deliberately not asserted
for this pointwise choice of tangent charts. -/
def pointwiseChartConnection : CovariantDerivative I E TM where
  toFun Z x := (trivializationAt E TM x).symmL ℝ x ∘L
    mvfderiv I (tangentSectionCoordinates x Z) x
  isCovariantDerivativeOnUniv := {
    add := by
      intro Z W x hZ hW _
      have hZc := mdifferentiableAt_tangentSectionCoordinates x
        (mem_baseSet_trivializationAt E TM x) hZ
      have hWc := mdifferentiableAt_tangentSectionCoordinates x
        (mem_baseSet_trivializationAt E TM x) hW
      have he : tangentSectionCoordinates x (Z + W) = fun y ↦
          tangentSectionCoordinates x Z y + tangentSectionCoordinates x W y := by
        funext y
        simp only [tangentSectionCoordinates, Pi.add_apply, map_add]
      rw [he, mvfderiv_fun_add hZc hWc]
      ext u
      simp only [ContinuousLinearMap.comp_apply, add_apply, map_add]
    leibniz := by
      intro Z f x hZ hf _
      have hZc := mdifferentiableAt_tangentSectionCoordinates x
        (mem_baseSet_trivializationAt E TM x) hZ
      have he : tangentSectionCoordinates x (f • Z) = fun y ↦
          f y • tangentSectionCoordinates x Z y := by
        funext y
        change (trivializationAt E TM x).continuousLinearMapAt ℝ y (f y • Z y) = _
        exact map_smul _ _ _
      rw [he, mvfderiv_fun_smul hf hZc]
      ext u
      simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, map_add, map_smul]
      simp only [tangentSectionCoordinates]
      rw [(trivializationAt E TM x).symmL_continuousLinearMapAt
        (mem_baseSet_trivializationAt E TM x)] }

/-- Formula for the explicit pointwise seed. -/
theorem pointwiseChartConnection_apply (Z : Π y, TM y) (x : M) (u : TM x) :
    pointwiseChartConnection (I := I) Z x u =
      (trivializationAt E TM x).symmL ℝ x
        (mvfderiv I (tangentSectionCoordinates x Z) x u) := rfl

end AlmostSchur
