/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.LocallyUniform

/-!
# Holomorphic maps with the compact-open topology

Holomorphic maps on an open domain form a closed complex submodule of the continuous maps
on that domain. The topology and uniformity are inherited from Mathlib's continuous-map
space, not from a global sup norm. In particular, the space is complete for Banach targets.

The zero extension below is only a device for expressing `AnalyticOnNhd` on the ambient
space. No continuity or analyticity at the boundary of the domain is asserted.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

open scoped Classical in
/-- Extend a continuous map on an open domain by zero; used only for local analytic predicates. -/
def openExtension (U : TopologicalSpace.Opens (ι → ℂ)) (f : C(U, F)) (z : ι → ℂ) : F :=
  if hz : z ∈ U then f ⟨z, hz⟩ else 0

omit [Fintype ι] [NormedSpace ℂ F] in
open scoped Classical in
theorem openExtension_apply (U : TopologicalSpace.Opens (ι → ℂ))
    (f : C(U, F)) {z : ι → ℂ} (hz : z ∈ U) : openExtension U f z = f ⟨z, hz⟩ :=
  dite_eq_left hz

omit [Fintype ι] [NormedSpace ℂ F] in
open scoped Classical in
@[simp] theorem openExtension_coe (U : TopologicalSpace.Opens (ι → ℂ))
    (f : C(U, F)) (z : U) : openExtension U f z = f z := by
  simp [openExtension, z.property]

open scoped Classical in
/-- Holomorphic maps are a submodule of continuous maps on the open domain. -/
def holomorphicSubmodule (U : TopologicalSpace.Opens (ι → ℂ)) : Submodule ℂ C(U, F) where
  carrier := {f | AnalyticOnNhd ℂ (openExtension U f) U}
  zero_mem' := by
    change AnalyticOnNhd ℂ (openExtension U 0) U
    have h : openExtension U (0 : C(U, F)) = fun _ => 0 := by
      funext z
      simp [openExtension]
    rw [h]
    exact analyticOnNhd_const
  add_mem' := by
    intro f g hf hg
    change AnalyticOnNhd ℂ (openExtension U (f + g)) U
    have h : openExtension U (f + g) = openExtension U f + openExtension U g := by
      funext z
      by_cases hz : z ∈ U <;> simp [openExtension, hz]
    rw [h]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change AnalyticOnNhd ℂ (openExtension U (c • f)) U
    have h : openExtension U (c • f) = c • openExtension U f := by
      funext z
      by_cases hz : z ∈ U <;> simp [openExtension, hz]
    rw [h]
    exact hf.const_smul

/-- Holomorphic maps on an open domain, with the induced compact-open topology and uniformity. -/
abbrev HolomorphicMap (U : TopologicalSpace.Opens (ι → ℂ)) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℂ F] := ↥(holomorphicSubmodule (F := F) U)

variable [CompleteSpace F]

omit [NormedSpace ℂ F] [CompleteSpace F] in
/-- Convergence in the continuous-map space is exactly locally uniform convergence of the
ambient extensions on the open domain. -/
theorem tendsto_iff_openExtension {U : TopologicalSpace.Opens (ι → ℂ)}
    {κ : Type*} {l : Filter κ} {f : κ → C(U, F)} {g : C(U, F)} :
    Tendsto f l (𝓝 g) ↔
      TendstoLocallyUniformlyOn (fun n => openExtension U (f n)) (openExtension U g) l U := by
  let := U.isOpen.locallyCompactSpace
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simp only [Function.comp_def, openExtension_coe]
  rfl

/-- Weierstrass convergence makes the holomorphic submodule closed. -/
theorem isClosed_holomorphicSubmodule (U : TopologicalSpace.Opens (ι → ℂ)) :
    IsClosed (holomorphicSubmodule (F := F) U : Set C(U, F)) := by
  rw [isClosed_iff_forall_filter]
  intro f l hl hmem hlim
  have hc : Tendsto (fun g : C(U, F) => g) l (𝓝 f) := hlim
  exact (tendsto_iff_openExtension.mp hc).analyticOnNhd_pi
    (le_principal_iff.mp hmem) U.isOpen

/-- The compact-open uniform space of holomorphic maps into a Banach space is complete. -/
instance (U : TopologicalSpace.Opens (ι → ℂ)) : CompleteSpace (HolomorphicMap U F) :=
  (isClosed_holomorphicSubmodule (F := F) U).isComplete.completeSpace_coe

omit [CompleteSpace F] in
/-- Evaluation at a point is continuous in the compact-open topology. -/
theorem continuous_holomorphicMap_eval (U : TopologicalSpace.Opens (ι → ℂ)) (z : U) :
    Continuous (fun f : HolomorphicMap U F => f.val z) :=
  (continuous_eval_const z).comp continuous_subtype_val

omit [CompleteSpace F] in
/-- The inherited topology on holomorphic maps is precisely locally uniform convergence. -/
theorem holomorphicMap_tendsto_iff {U : TopologicalSpace.Opens (ι → ℂ)}
    {κ : Type*} {l : Filter κ} {f : κ → HolomorphicMap U F} {g : HolomorphicMap U F} :
    Tendsto f l (𝓝 g) ↔ TendstoLocallyUniformlyOn
      (fun n => openExtension U (f n).val) (openExtension U g.val) l U := by
  rw [tendsto_subtype_rng, tendsto_iff_openExtension]

/-- Coordinate differentiation as an operator on holomorphic maps. -/
def holomorphicPartialDeriv (U : TopologicalSpace.Opens (ι → ℂ)) (i : ι)
    (f : HolomorphicMap U F) : HolomorphicMap U F := by
  have ha := f.property.partialDeriv U.isOpen i
  refine ⟨⟨fun z => partialDeriv i (openExtension U f.val) z,
    ha.continuousOn.domRestrict⟩, ?_⟩
  apply AnalyticOnNhd.congr U.isOpen ha
  intro z hz
  rw [openExtension_apply U _ hz]
  rfl

/-- Coordinate differentiation is continuous for the compact-open topology. -/
theorem continuous_holomorphicPartialDeriv (U : TopologicalSpace.Opens (ι → ℂ)) (i : ι) :
    Continuous (holomorphicPartialDeriv (F := F) U i) := by
  rw [continuous_iff_continuousAt]
  intro f
  change Tendsto _ (𝓝 f) _
  rw [holomorphicMap_tendsto_iff]
  have hlim := (holomorphicMap_tendsto_iff (f := fun g : HolomorphicMap U F => g)).mp
    (tendsto_id : Tendsto (fun g : HolomorphicMap U F => g) (𝓝 f) (𝓝 f))
  have hd := hlim.partialDeriv (Eventually.of_forall fun g => g.property) U.isOpen i
  apply (hd.congr (fun g z hz => ?_)).congr_right (fun z hz => ?_)
  all_goals
    rw [openExtension_apply U _ hz]
    rfl

omit [CompleteSpace F] in
/-- Restriction to a smaller open domain preserves holomorphy. -/
def holomorphicRestrict {U V : TopologicalSpace.Opens (ι → ℂ)} (hVU : V ≤ U)
    (f : HolomorphicMap U F) : HolomorphicMap V F := by
  let inc : C(V, U) := ⟨fun z => ⟨z, hVU z.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  refine ⟨f.val.comp inc, ?_⟩
  apply AnalyticOnNhd.congr V.isOpen (f.property.mono hVU)
  intro z hz
  rw [openExtension_apply U _ (hVU hz), openExtension_apply V _ hz]
  rfl

omit [CompleteSpace F] in
/-- Restriction is continuous for the compact-open topology. -/
theorem continuous_holomorphicRestrict {U V : TopologicalSpace.Opens (ι → ℂ)}
    (hVU : V ≤ U) : Continuous (holomorphicRestrict (F := F) hVU) := by
  apply Continuous.subtype_mk
  exact (ContinuousMap.continuous_precomp
    ⟨fun z : V => (⟨z, hVU z.property⟩ : U), continuous_subtype_val.subtype_mk _⟩).comp
      continuous_subtype_val

end SeveralComplexVariables

end
