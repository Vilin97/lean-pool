/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacFunctorial.TraceIntegral
import LeanPool.JacobianDiffgeo.JacFunctorial.TraceLaws
import LeanPool.JacobianDiffgeo.JacFunctorial.PeriodMaps

/-!
# The pullback map on Jacobians (jacobian-functoriality §8, pullback half)

Unit: jacobian-functoriality. `RS.pullbackT` (the period-space linear map induced by
`Form1.trace`'s `dualMap`), `RS.pullbackT_periodVector` (its action on period vectors),
`RS.periodSubgroup_le_comap_pullbackT` (`hT` for the pullback direction — **exact** membership
via `RS.periodVector_traceForm_mem`, after conjugating the loop to a regular basepoint
(`RS.period_conj`) and perturbing it off the finite branch locus
(`RS.Loop.exists_homotopic_avoiding` + `RS.period_congr_homotopic`)), and the assembly
**`Jacobian.pullback`** via `Jacobian.inducedHom` (same-universe convention, see
`PeriodMaps.lean`'s universe warning).
-/

open scoped ContDiff Manifold
open IsManifold Module

noncomputable section

namespace RS

universe u

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The induced `ℂ`-linear map on period spaces for the pullback direction, from
`Form1.trace f hf`'s `dualMap` (covariant trace transposes to the contravariant direction:
`Dual (Form1 Y) →ₗ Dual (Form1 X)`, i.e. period space of `Y` to period space of `X`). -/
noncomputable def pullbackT (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (genus Y) → ℂ) →ₗ[ℂ] (Fin (genus X) → ℂ) :=
  (periodCoordEquiv X).toLinearMap ∘ₗ
    ((Form1.trace f hf).dualMap ∘ₗ (periodCoordEquiv Y).symm.toLinearMap)

omit [ConnectedSpace Y] in
/-- The pullback period map computed at a based loop. -/
theorem pullbackT_periodVector (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {y : Y}
    (γ : Path y y) :
    pullbackT f hf (periodVector (basis Y) γ)
      = fun i => pathIntegral γ (Form1.trace f hf (basis X i)) := by
  have hsymm : (periodCoordEquiv Y).symm (periodVector (basis Y) γ) = pathIntegralₗ γ := by
    apply (periodCoordEquiv Y).injective
    rw [(periodCoordEquiv Y).apply_symm_apply]
    funext j
    rw [periodCoordEquiv_apply]
    rfl
  funext i
  change periodCoordEquiv X ((Form1.trace f hf).dualMap
      ((periodCoordEquiv Y).symm (periodVector (basis Y) γ))) i = _
  rw [hsymm, periodCoordEquiv_apply, LinearMap.dualMap_apply]
  rfl

/-- `hT` for the pullback direction (§8.3): exact membership, via basepoint conjugation +
off-branch perturbation + the loop decomposition of the trace integral. -/
theorem periodSubgroup_le_comap_pullbackT (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    RS.periodSubgroup Y ≤ (RS.periodSubgroup X).topologicalClosure.comap
      (pullbackT f hf).toAddMonoidHom := by
  rw [periodSubgroup, AddSubgroup.closure_le]
  rintro v ⟨γ, rfl⟩
  change pullbackT f hf (periodVector (basis Y) γ) ∈ (periodSubgroup X).topologicalClosure
  rw [pullbackT_periodVector]
  by_cases hc : ∃ c, ∀ x, f x = c
  · have h0 : (fun i => pathIntegral γ (Form1.trace f hf (basis X i)))
        = (0 : Fin (genus X) → ℂ) := by
      funext i
      rw [Form1.trace_of_forall_eq hf hc]
      change pathIntegral γ ((0 : Form1 X →ₗ[ℂ] Form1 Y) (basis X i)) = 0
      rw [LinearMap.zero_apply, pathIntegral_zero_form]
    rw [h0]
    exact zero_mem _
  · obtain ⟨y', hy'⟩ := RS.exists_isRegularValue hf hc
    set σ : Path y' (Classical.arbitrary Y) :=
      PathConnectedSpace.somePath y' (Classical.arbitrary Y) with hσ_def
    set γ₁ : Path y' y' := (σ.trans γ).trans σ.symm with hγ₁_def
    have hy'B : y' ∉ RS.branchLocus f :=
      (RS.isRegularValue_iff_notMem_branchLocus f y').mp hy'
    obtain ⟨γ₂, hhom, hdisj⟩ := RS.Loop.exists_homotopic_avoiding γ₁
      (RS.branchLocus_finite hf hc) hy'B
    have hreg : ∀ s : unitInterval, RS.IsRegularValue f (γ₂ s) := by
      intro s
      rw [RS.isRegularValue_iff_notMem_branchLocus]
      exact fun hB => (Set.disjoint_left.mp hdisj (Set.mem_range_self s)) hB
    have heq : (fun i => pathIntegral γ (Form1.trace f hf (basis X i)))
        = fun i => pathIntegral γ₂ (traceForm hf hc (basis X i)) := by
      funext i
      have h2 : pathIntegral γ₁ (Form1.trace f hf (basis X i))
          = pathIntegral γ₂ (Form1.trace f hf (basis X i)) :=
        period_congr_homotopic hhom _
      have h1 : pathIntegral γ₁ (Form1.trace f hf (basis X i))
          = pathIntegral γ (Form1.trace f hf (basis X i)) :=
        period_conj σ γ _
      rw [← Form1.trace_apply hf hc (basis X i), ← h2, h1]
    rw [heq]
    exact AddSubgroup.le_topologicalClosure _
      (periodVector_traceForm_mem (hf := hf) (hne := hc) γ₂ hreg)

section SameUniverse

/- Same-universe convention as `PeriodMaps.lean` (see the universe warning there):
`Jacobian.inducedHom` demands both surfaces in ONE `Type u`. -/
variable {X' : Type u} [TopologicalSpace X'] [T2Space X'] [CompactSpace X'] [ConnectedSpace X']
  [ChartedSpace ℂ X'] [IsManifold 𝓘(ℂ) ω X']
variable {Y' : Type u} [TopologicalSpace Y'] [T2Space Y'] [CompactSpace Y'] [ConnectedSpace Y']
  [ChartedSpace ℂ Y'] [IsManifold 𝓘(ℂ) ω Y']

/-- **`Jacobian.pullback` (§8.4)**: the pullback map between Jacobians associated to a
holomorphic map of the underlying curves. Equal to the zero map if the map on curves is
constant (`Form1.trace`'s convention). -/
noncomputable def Jacobian.pullback (f : X' → Y') (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y' →ₜ+ Jacobian X' :=
  Jacobian.inducedHom (periodSubgroup_le_comap_pullbackT f hf)

end SameUniverse

end RS

end
