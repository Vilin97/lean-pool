/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyLieBracketMixedRegularity
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Mixed time derivatives of manifold Lie brackets

Transport the Euclidean mixed-derivative theorem through a fixed tangent-bundle chart.
The moving section is jointly C² as a map into the tangent bundle. Its time velocity
is specified in each fixed tangent fibre. No bracket derivative is assumed.
-/

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace PoincareCurvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

omit [CompleteSpace E] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] in
/-- On the chart target, pulling a tangent field back by the inverse chart is
exactly its coordinate in the tangent-bundle trivialization. -/
theorem mpullbackWithin_extChartAt_symm_eq_trivialization
    (Y : Π y : M, TM y) (x : M) {z : E}
    (hz : z ∈ (extChartAt I x).target) :
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Y (range I) z =
      (trivializationAt E TM x
        (TotalSpace.mk' E ((extChartAt I x).symm z) (Y ((extChartAt I x).symm z)))).2 := by
  rw [VectorField.mpullbackWithin_apply,
    ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hz)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hz)]
  have hx : (extChartAt I x).symm z ∈ (chartAt H x).source := by
    simpa only [extChartAt_source] using (extChartAt I x).map_target hz
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hx]
  exact (trivializationAt E TM x).continuousLinearMapAt_apply_of_mem (R := ℝ)
    (by simpa using hx) _

omit [CompleteSpace E] in
/-- Joint regularity of a totalized moving tangent section gives joint
regularity of its vector-valued coordinate field in a fixed chart. -/
theorem contDiffAt_mpullbackWithin_extChartAt_symm_of_joint_contMDiffAt
    (Y : ℝ → Π y : M, TM y) {t : ℝ} {x : M}
    (hY : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (Y p.1 p.2)) (t, x)) :
    ContDiffAt ℝ 2
      (fun p : ℝ × E => VectorField.mpullbackWithin 𝓘(ℝ, E) I
        (extChartAt I x).symm (Y p.1) (range I) p.2)
      (t, extChartAt I x x) := by
  let e := trivializationAt E TM x
  have hcoord : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, E) 2
      (fun p : ℝ × M => (e (TotalSpace.mk' E p.2 (Y p.1 p.2))).2) (t, x) :=
    (e.contMDiffAt_iff (by simp [e])).mp hY |>.2
  have hchart := (contMDiffAt_iff.mp hcoord).2
  rw [extChartAt_prod, ModelWithCorners.Boundaryless.range_eq_univ] at hchart
  have hchart' : ContDiffAt ℝ 2
      (fun p : ℝ × E => (e (TotalSpace.mk' E ((extChartAt I x).symm p.2)
        (Y p.1 ((extChartAt I x).symm p.2)))).2) (t, extChartAt I x x) := by
    simpa [ContDiffAt, Function.comp_def, PartialEquiv.prod_coe_symm,
      chartAt_self_eq] using hchart
  apply hchart'.congr_of_eventuallyEq
  have htarget : ∀ᶠ p : ℝ × E in 𝓝 (t, extChartAt I x x),
      p.2 ∈ (extChartAt I x).target :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds x)
  filter_upwards [htarget] with p hp
  exact mpullbackWithin_extChartAt_symm_eq_trivialization (Y p.1) x hp
/-- Differentiate the manifold Lie bracket in its moving left slot. Joint C²
regularity of the totalized section supplies the time--space interchange. -/
theorem hasDerivAt_mlieBracket_left_of_joint_contMDiffAt
    (Y : ℝ → Π y : M, TM y) (Ydot W : Π y : M, TM y)
    {t : ℝ} {x : M}
    (hY : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (Y p.1 p.2)) (t, x))
    (hYtime : ∀ y : M, HasDerivAt (fun τ : ℝ => Y τ y) (Ydot y) t)
    (hW : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% W) x) :
    HasDerivAt (fun τ => VectorField.mlieBracket I (Y τ) W x)
      (VectorField.mlieBracket I Ydot W x) t := by
  let : ∀ y : M, NormedAddCommGroup (TM y) := fun y =>
    { (inferInstance : NormedAddCommGroup E) with
      toAddCommGroup := (inferInstance : AddCommGroup (TM y)) }
  let : ∀ y : M, NormedSpace ℝ (TM y) := fun y =>
    { (inferInstance : NormedSpace ℝ E) with
      toModule := (inferInstance : Module ℝ (TM y)) }
  let U : ℝ → E → E := fun τ => VectorField.mpullbackWithin 𝓘(ℝ, E) I
    (extChartAt I x).symm (Y τ) (range I)
  let Udot : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I
    (extChartAt I x).symm Ydot (range I)
  let V : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I
    (extChartAt I x).symm W (range I)
  have hU : ContDiffAt ℝ 2 (fun p : ℝ × E => U p.1 p.2)
      (t, extChartAt I x x) :=
    contDiffAt_mpullbackWithin_extChartAt_symm_of_joint_contMDiffAt Y hY
  have hUtime : ∀ z : E, HasDerivAt (fun τ => U τ z) (Udot z) t := by
    intro z
    let L : TM ((extChartAt I x).symm z) →L[ℝ] E :=
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) z).inverse
    exact L.hasFDerivAt.comp_hasDerivAt t (hYtime ((extChartAt I x).symm z))
  have hVwithin := contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp
    (VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm
      (s := Set.univ) (n := 2) hW.contMDiffWithinAt uniqueMDiffOn_univ
      (Set.mem_univ x) (by norm_num))
  simp only [Set.preimage_univ, Set.inter_univ] at hVwithin
  have hV : ContDiffAt ℝ 1 V (extChartAt I x x) :=
    hVwithin.contDiffAt (extChartAt_target_mem_nhds x)
  have hbracket := hasDerivAt_lieBracket_left_of_joint_contDiffAt U Udot V hU hUtime hV
  let L : E →L[ℝ] TM x := (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x).inverse
  have htransport := L.hasFDerivAt.comp_hasDerivAt t hbracket
  simpa only [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply,
    Set.preimage_univ, Set.univ_inter,
    ModelWithCorners.Boundaryless.range_eq_univ, VectorField.lieBracketWithin_univ,
    Function.comp_def, U, Udot, V, L] using! htransport

/-- The corresponding derivative in the right slot follows by antisymmetry. -/
theorem hasDerivAt_mlieBracket_right_of_joint_contMDiffAt
    (Y : ℝ → Π y : M, TM y) (Ydot W : Π y : M, TM y)
    {t : ℝ} {x : M}
    (hY : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (Y p.1 p.2)) (t, x))
    (hYtime : ∀ y : M, HasDerivAt (fun τ : ℝ => Y τ y) (Ydot y) t)
    (hW : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% W) x) :
    HasDerivAt (fun τ => VectorField.mlieBracket I W (Y τ) x)
      (VectorField.mlieBracket I W Ydot x) t := by
  let : NormedAddCommGroup (TM x) :=
    { (inferInstance : NormedAddCommGroup E) with
      toAddCommGroup := (inferInstance : AddCommGroup (TM x)) }
  let : NormedSpace ℝ (TM x) :=
    { (inferInstance : NormedSpace ℝ E) with
      toModule := (inferInstance : Module ℝ (TM x)) }
  have h := (hasDerivAt_mlieBracket_left_of_joint_contMDiffAt Y Ydot W hY hYtime hW).neg
  have h' := h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun τ =>
      VectorField.mlieBracket_swap_apply (I := I) (V := W) (W := Y τ) (x := x)))
  exact h'.congr_deriv (VectorField.mlieBracket_swap_apply
    (I := I) (V := W) (W := Ydot) (x := x)).symm

end PoincareCurvature
