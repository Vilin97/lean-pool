/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacobianConstruction.Torus

/-!
# The `ULift` shell: transporting `ChartedSpace`/`IsManifold`/`LieAddGroup` along `Homeomorph.ulift`

Unit: jacobian-construction (`docs/design/jacobian-construction.md` §2, §7). The challenge's
`Jacobian X : Type u` is universe-polymorphic in `X`, but the honest construction
`Jac₀ X := (Fin (genus X) → ℂ) ⧸ Λ` lives in `Type 0`; `Jacobian X := ULift.{u} (Jac₀ X)` bridges
the two. This file builds the (specialized, per design's R1 fallback) transport toolkit that
moves `ChartedSpace`/`IsManifold`/`LieAddGroup` across `Homeomorph.ulift : ULift (V ⧸ L) ≃ₜ V ⧸ L`,
for the same `V`, `L` as `Torus.lean`.

The key simplification throughout: `ULift.up`/`ULift.down` are an **exact** (not merely
"eventual", unlike the lattice-shift business in `Torus.lean`) pair of mutually inverse
continuous maps, so every chart composite involving them cancels by `rfl`. Consequently:

* `ChartedSpace`/`IsManifold` transport directly, reusing `Torus.lean`'s
  `analyticOnNhd_chartAt'_trans` verbatim (the `ULift`-wrapped transition function/source agree
  *exactly*, not just up to congruence, with the unwrapped one).
* `LieAddGroup` transports via a cleaner route: `ULift.down`/`ULift.up` are themselves `ω`-smooth
  maps between `ULift (V ⧸ L)` and `V ⧸ L` (their chart composite, in matching charts at the same
  representative, is the identity on an open set), so addition/negation on `ULift (V ⧸ L)` factor
  through `V ⧸ L`'s own `contMDiff_add_torus`/`contMDiff_neg_torus` by composition — no new
  analyticity computation.
-/

open scoped ContDiff Manifold Pointwise
open Set Filter Topology Metric

universe u

noncomputable section

namespace RS

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable (L : AddSubgroup V) [DiscreteTopology L]

/-! ## `ChartedSpace`/`IsManifold` -/

/-- The chart family for `ULift (V ⧸ L)`: `chartAt' L x`, transported through
`Homeomorph.ulift`. -/
def uliftChartAt (x : V) : OpenPartialHomeomorph (ULift.{u} (V ⧸ L)) V :=
  (Homeomorph.ulift (X := V ⧸ L)).toOpenPartialHomeomorph.trans (chartAt' L x)

omit [CompleteSpace V] [NormedSpace ℂ V] in
theorem uliftChartAt_mem_source (q : ULift.{u} (V ⧸ L)) :
    q ∈ (uliftChartAt L (Function.surjInv QuotientAddGroup.mk_surjective q.down)).source := by
  rw [uliftChartAt, OpenPartialHomeomorph.trans_source]
  exact ⟨trivial, chartAt'_mem_source L q.down⟩

instance instChartedSpaceULift : ChartedSpace V (ULift.{u} (V ⧸ L)) :=
  chartedSpaceOfFamily' (uliftChartAt L)
    (fun q => Function.surjInv QuotientAddGroup.mk_surjective q.down) (uliftChartAt_mem_source L)

omit [CompleteSpace V] [NormedSpace ℂ V] in
theorem chartAt_ulift_eq (q : ULift.{u} (V ⧸ L)) :
    chartAt V q = uliftChartAt L (Function.surjInv QuotientAddGroup.mk_surjective q.down) := rfl

omit [CompleteSpace V] [NormedSpace ℂ V] in
/-- `Homeomorph.ulift`'s associated `OpenPartialHomeomorph.symm`, precomposed into a
`uliftChartAt`, cancels by `rfl` (`PartialEquiv.coe_trans_symm`). -/
theorem uliftChartAt_symm_apply (x w : V) :
    (uliftChartAt L x).symm w = ULift.up ((chartAt' L x).symm w) := rfl

omit [CompleteSpace V] [NormedSpace ℂ V] in
theorem uliftChartAt_target (x : V) : (uliftChartAt L x).target = (chartAt' L x).target := by
  rw [uliftChartAt, OpenPartialHomeomorph.trans_target]
  simp

omit [CompleteSpace V] [NormedSpace ℂ V] in
theorem uliftChartAt_source' (x : V) :
    (uliftChartAt L x).source = ULift.down ⁻¹' (chartAt' L x).source := by
  rw [uliftChartAt, OpenPartialHomeomorph.trans_source]
  simp
  rfl

omit [CompleteSpace V] [NormedSpace ℂ V] in
/-- The `ULift`-wrapped transition function agrees *exactly* with the unwrapped one (no
neighborhood needed: `ULift.up`/`.down` cancel by `rfl`). -/
theorem uliftChartAt_trans_eq (x x' : V) :
    (⇑((uliftChartAt L x).symm ≫ₕ uliftChartAt L x') : V → V)
      = ⇑((chartAt' L x).symm ≫ₕ chartAt' L x') := by
  funext w
  simp only [uliftChartAt, OpenPartialHomeomorph.trans_apply]
  rfl

omit [CompleteSpace V] [NormedSpace ℂ V] in
theorem uliftChartAt_trans_source (x x' : V) :
    ((uliftChartAt L x).symm ≫ₕ uliftChartAt L x').source
      = ((chartAt' L x).symm ≫ₕ chartAt' L x').source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.symm_source, uliftChartAt_target]
  congr 1
  ext w
  simp only [Set.mem_preimage, uliftChartAt_symm_apply, uliftChartAt_source']

/-- `ULift (V ⧸ L)` is an `ω`-manifold, by transporting `Torus.lean`'s
`analyticOnNhd_chartAt'_trans` exactly through the (`rfl`-cancelling) `ULift` wrapping. -/
instance instIsManifoldULift : IsManifold 𝓘(ℂ, V) ω (ULift.{u} (V ⧸ L)) := by
  apply isManifold_of_family' (uliftChartAt L)
    (fun q => Function.surjInv QuotientAddGroup.mk_surjective q.down) (uliftChartAt_mem_source L)
  intro x x'
  rw [uliftChartAt_trans_source L x x']
  intro w hw
  rw [show (⇑((uliftChartAt L x).symm ≫ₕ uliftChartAt L x') : V → V)
      = ⇑((chartAt' L x).symm ≫ₕ chartAt' L x') from uliftChartAt_trans_eq L x x']
  exact analyticOnNhd_chartAt'_trans L x x' w hw

/-! ## `ULift.down`/`ULift.up` are `ω`-smooth -/

omit [NormedSpace ℂ V] [CompleteSpace V] [DiscreteTopology ↥L] in
theorem continuous_uliftDown : Continuous (ULift.down : ULift.{u} (V ⧸ L) → V ⧸ L) :=
  (Homeomorph.ulift (X := V ⧸ L)).continuous

omit [NormedSpace ℂ V] [CompleteSpace V] [DiscreteTopology ↥L] in
theorem continuous_uliftUp : Continuous (ULift.up.{u} : V ⧸ L → ULift.{u} (V ⧸ L)) :=
  (Homeomorph.ulift (X := V ⧸ L)).symm.continuous

omit [CompleteSpace V] in
theorem extChartAt_ulift_apply_eq (q q' : ULift.{u} (V ⧸ L)) :
    extChartAt 𝓘(ℂ, V) q q'
      = uliftChartAt L (Function.surjInv QuotientAddGroup.mk_surjective q.down) q' := by
  rw [extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe, id_eq, chartAt_ulift_eq]

omit [CompleteSpace V] in
theorem extChartAt_ulift_symm_apply_eq (q : ULift.{u} (V ⧸ L)) (w : V) :
    (extChartAt 𝓘(ℂ, V) q).symm w
      = ULift.up ((chartAt' L (Function.surjInv QuotientAddGroup.mk_surjective q.down)).symm w) :=
          by
  rw [extChartAt_coe_symm, Function.comp_apply, modelWithCornersSelf_coe_symm, id_eq,
    chartAt_ulift_eq, uliftChartAt]
  rfl

omit [CompleteSpace V] in
theorem extChartAt_ulift_self_eq (q : ULift.{u} (V ⧸ L)) :
    extChartAt 𝓘(ℂ, V) q q = Function.surjInv QuotientAddGroup.mk_surjective q.down := by
  rw [extChartAt_ulift_apply_eq]
  set x := Function.surjInv QuotientAddGroup.mk_surjective q.down
  show uliftChartAt L x q = x
  rw [uliftChartAt, OpenPartialHomeomorph.trans_apply]
  change chartAt' L x q.down = x
  have hxq : (QuotientAddGroup.mk x : V ⧸ L) = q.down := Function.surjInv_eq _ q.down
  rw [← hxq]
  exact chartAt'_apply_mk L (Metric.mem_ball_self (injRadius_pos L))

/-- `ULift.down` is `ω`-smooth: in matching charts at the *same* representative, the composite is
the identity on the (open) chart target. -/
theorem contMDiff_uliftDown : ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, V) ω
    (ULift.down : ULift.{u} (V ⧸ L) → V ⧸ L) := by
  intro q
  set x := Function.surjInv QuotientAddGroup.mk_surjective q.down with hx_def
  rw [contMDiffAt_iff]
  refine ⟨(continuous_uliftDown L).continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ]
  have hpt : extChartAt 𝓘(ℂ, V) q q = x := extChartAt_ulift_self_eq L q
  rw [hpt]
  have hexact : ∀ w : V, extChartAt 𝓘(ℂ, V) q.down (ULift.down ((extChartAt 𝓘(ℂ, V) q).symm w))
      = chartAt' L x ((chartAt' L x).symm w) := by
    intro w
    rw [extChartAt_ulift_symm_apply_eq, extChartAt_apply_eq]
  have htarget : x ∈ (chartAt' L x).target := by
    rw [chartAt'_target]; exact Metric.mem_ball_self (injRadius_pos L)
  have hgoal_eq :
      (fun w : V => extChartAt 𝓘(ℂ, V) q.down (ULift.down ((extChartAt 𝓘(ℂ, V) q).symm w)))
      =ᶠ[𝓝 x] (id : V → V) := by
    filter_upwards [(chartAt' L x).open_target.mem_nhds htarget] with w hw
    rw [hexact w]
    exact (chartAt' L x).right_inv hw
  exact ((analyticAt_id).congr hgoal_eq.symm).contDiffAt

/-- `ULift.up` is `ω`-smooth: mirror-image argument to `contMDiff_uliftDown`. -/
theorem contMDiff_uliftUp : ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, V) ω
    (ULift.up.{u} : V ⧸ L → ULift.{u} (V ⧸ L)) := by
  intro q
  set x := Function.surjInv QuotientAddGroup.mk_surjective q with hx_def
  rw [contMDiffAt_iff]
  refine ⟨(continuous_uliftUp L).continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ]
  have hpt : extChartAt 𝓘(ℂ, V) q q = x := extChartAt_self_eq L q
  rw [hpt]
  have hexact : ∀ w : V,
      extChartAt 𝓘(ℂ, V) (ULift.up.{u} q) (ULift.up.{u} ((extChartAt 𝓘(ℂ, V) q).symm w))
      = chartAt' L x (QuotientAddGroup.mk w) := by
    intro w
    rw [extChartAt_symm_apply_eq, extChartAt_ulift_apply_eq]
    rfl
  have htarget : x ∈ ball x (injRadius L) := Metric.mem_ball_self (injRadius_pos L)
  have hgoal_eq : (fun w : V =>
      extChartAt 𝓘(ℂ, V) (ULift.up.{u} q) (ULift.up.{u} ((extChartAt 𝓘(ℂ, V) q).symm w)))
      =ᶠ[𝓝 x] (id : V → V) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds htarget] with w hw
    rw [hexact w]
    exact chartAt'_apply_mk L hw
  exact ((analyticAt_id).congr hgoal_eq.symm).contDiffAt

/-! ## `LieAddGroup` for `ULift (V ⧸ L)` -/

theorem contMDiff_add_ulift :
    ContMDiff (𝓘(ℂ, V).prod 𝓘(ℂ, V)) 𝓘(ℂ, V) ω
      (fun p : ULift.{u} (V ⧸ L) × ULift.{u} (V ⧸ L) => p.1 + p.2) := by
  have heq : (fun p : ULift.{u} (V ⧸ L) × ULift.{u} (V ⧸ L) => p.1 + p.2)
      = ULift.up ∘ (fun p : (V ⧸ L) × (V ⧸ L) => p.1 + p.2) ∘
        (Prod.map ULift.down ULift.down) := by
    funext p; rfl
  rw [heq]
  exact (contMDiff_uliftUp L).comp
    ((contMDiff_add_torus L).comp ((contMDiff_uliftDown L).prodMap (contMDiff_uliftDown L)))

theorem contMDiff_neg_ulift :
    ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, V) ω (fun q : ULift.{u} (V ⧸ L) => -q) := by
  have heq : (fun q : ULift.{u} (V ⧸ L) => -q) = ULift.up ∘ (fun q : V ⧸ L => -q) ∘ ULift.down := by
    funext q; rfl
  rw [heq]
  exact (contMDiff_uliftUp L).comp ((contMDiff_neg_torus L).comp (contMDiff_uliftDown L))

instance instLieAddGroupULift : LieAddGroup 𝓘(ℂ, V) ω (ULift.{u} (V ⧸ L)) :=
  { contMDiff_add := contMDiff_add_ulift L
    contMDiff_neg := contMDiff_neg_ulift L }

end RS
