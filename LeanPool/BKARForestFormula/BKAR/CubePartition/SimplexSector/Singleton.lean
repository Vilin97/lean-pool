/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasureSmoothness

/-! # Simplex-sector conversion: one edge

The one-dimensional case of the simplex-sector conversion: for a forest
with a single edge, the recursive ordered contribution is the set integral
over `[0, 1]` in the unique cube coordinate, identified through the
`funUnique` measure-preserving equivalence, and hence equals the closed
ordered cube-sector contribution.
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edges_eq_singleton_of_singleton_mem_edgeOrders
    (F : Forest V) {e : Edge V} (horder : [e] ∈ F.edgeOrders) :
    F.edges = {e} := by
  have hset := F.toFinset_eq_of_mem_edgeOrders horder
  simpa using hset.symm

/-- The unique edge parameter when the forest consists of the specified single edge. -/
@[reducible] def uniqueEdgeParamOfEdgesSingleton
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e}) :
    Unique F.EdgeParam where
  default := ⟨e, by rw [hedges]; exact Finset.mem_singleton_self e⟩
  uniq := by
    intro p
    apply Subtype.ext
    have hp : p.val ∈ ({e} : Finset (Edge V)) := by
      rw [← hedges]
      exact p.property
    exact Finset.mem_singleton.mp hp

theorem paramsOfOrder_singleton_eq_funUnique_symm
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e})
    (t : ℝ) :
    F.paramsOfOrder [e] [t] =
      (@MeasurableEquiv.funUnique F.EdgeParam ℝ
        (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance).symm t := by
  let : Unique F.EdgeParam := F.uniqueEdgeParamOfEdgesSingleton hedges
  funext p
  have hp : p.val = e := by
    have hp_mem : p.val ∈ ({e} : Finset (Edge V)) := by
      rw [← hedges]
      exact p.property
    exact Finset.mem_singleton.mp hp_mem
  have hp_eq :
      p = (default : F.EdgeParam) := Subsingleton.elim p default
  rw [hp_eq]
  have hdefault :
      (default : F.EdgeParam) =
        ⟨e, by rw [hedges]; exact Finset.mem_singleton_self e⟩ :=
    Subtype.ext (by
      change (default : F.EdgeParam).val = e
      rw [← hp]
      exact congrArg Subtype.val hp_eq.symm)
  rw [hdefault]
  rw [F.paramsOfOrder_cons_self e [] t []]
  simp

theorem orderedCubeSimplex_singleton_eq_funUnique_preimage_Icc
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e}) :
    F.orderedCubeSimplex [e] =
      (@MeasurableEquiv.funUnique F.EdgeParam ℝ
        (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance) ⁻¹'
        Set.Icc (0 : ℝ) 1 := by
  let : Unique F.EdgeParam := F.uniqueEdgeParamOfEdgesSingleton hedges
  ext u
  have he : e ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_singleton_self e
  let p₀ : F.EdgeParam := ⟨e, he⟩
  have hunit :
      u ∈ F.unitCube ↔ (0 : ℝ) ≤ u p₀ ∧ u p₀ ≤ 1 := by
    rw [F.mem_unitCube_iff]
    constructor
    · intro hu
      exact hu p₀
    · intro hu p
      rw [Subsingleton.elim p p₀]
      exact hu
  have hparam : F.paramValue u e = u p₀ := by
    exact F.paramValue_of_mem u he
  have hdefault : (default : F.EdgeParam) = p₀ :=
    Subsingleton.elim default p₀
  rw [mem_orderedCubeSimplex_iff]
  simp [hunit, hparam, OrderedSimplexParams, hdefault]

theorem measurePreserving_funUnique_edgeParam_singleton
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e}) :
    MeasurePreserving
      (@MeasurableEquiv.funUnique F.EdgeParam ℝ
        (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance)
      (volume : Measure (F.EdgeParam → ℝ)) (volume : Measure ℝ) := by
  let : Unique F.EdgeParam := F.uniqueEdgeParamOfEdgesSingleton hedges
  rw [volume_pi]
  convert measurePreserving_funUnique (volume : Measure ℝ) F.EdgeParam using 2

omit [Fintype V] in
omit [DecidableEq V] in
/-- The one-dimensional ordered simplex integral is the set integral over `[0, 1]`. -/
theorem orderedSimplexIntegral_singleton_eq_setIntegral_Icc
    (e : Edge V) (f : ℝ → ℝ) :
    orderedSimplexIntegral [e] (fun ts => f (ts.getD 0 0)) =
      ∫ t in Set.Icc (0 : ℝ) 1, f t := by
  classical
  rw [orderedSimplexIntegral_singleton]
  change (∫ t in 0..(1 : ℝ), f t) =
    ∫ t in Set.Icc (0 : ℝ) 1, f t
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [setIntegral_congr_set Ioc_ae_eq_Icc]

/--
First step of the simplex-sector conversion for one edge: the recursive
ordered contribution is the
ordinary set integral over the one-dimensional simplex coordinate. The
remaining singleton sector bridge is exactly the `funUnique` measure-preserving
identification of that coordinate with the one-edge cube.
-/
theorem orderedContribution_singleton_eq_setIntegral_Icc_funUnique
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e})
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedContribution [e] ρ =
      ∫ t in Set.Icc (0 : ℝ) 1,
        mixedPartialList [e].reverse ρ
          (F.standardInterp
            ((@MeasurableEquiv.funUnique F.EdgeParam ℝ
              (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance).symm t)) := by
  let : Unique F.EdgeParam := F.uniqueEdgeParamOfEdgesSingleton hedges
  let φ : (F.EdgeParam → ℝ) ≃ᵐ ℝ :=
    @MeasurableEquiv.funUnique F.EdgeParam ℝ
      (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance
  let H : (F.EdgeParam → ℝ) → ℝ :=
    fun u => mixedPartialList [e].reverse ρ (F.standardInterp u)
  have hparams :
      ∀ t : ℝ, H (F.paramsOfOrder [e] [t]) = H (φ.symm t) := by
    intro t
    rw [F.paramsOfOrder_singleton_eq_funUnique_symm hedges t]
  calc
    F.orderedContribution [e] ρ
        = ∫ t in 0..(1 : ℝ), H (F.paramsOfOrder [e] [t]) := by
          rw [orderedContribution, orderedSimplexIntegral_singleton]
    _ = ∫ t in 0..(1 : ℝ), H (φ.symm t) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          exact hparams t
    _ = ∫ t in Set.Icc (0 : ℝ) 1, H (φ.symm t) := by
          rw [intervalIntegral.integral_of_le zero_le_one]
          rw [setIntegral_congr_set Ioc_ae_eq_Icc]
    _ = ∫ t in Set.Icc (0 : ℝ) 1,
          mixedPartialList [e].reverse ρ (F.standardInterp (φ.symm t)) := rfl

/--
The simplex-sector conversion in the first nontrivial dimension: the nested
ordered-simplex integral for
a one-edge canonical order is exactly the set integral over the corresponding
closed ordered cube sector.
-/
theorem orderedContribution_singleton_eq_orderedCubeSectorContribution
    (F : Forest V) {e : Edge V} (horder : [e] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedContribution [e] ρ =
      F.orderedCubeSectorContribution [e] ρ := by
  let hedges := F.edges_eq_singleton_of_singleton_mem_edgeOrders horder
  let : Unique F.EdgeParam := F.uniqueEdgeParamOfEdgesSingleton hedges
  let φ : (F.EdgeParam → ℝ) ≃ᵐ ℝ :=
    @MeasurableEquiv.funUnique F.EdgeParam ℝ
      (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance
  let H : (F.EdgeParam → ℝ) → ℝ :=
    fun u => mixedPartialList [e].reverse ρ (F.standardInterp u)
  have hsector :
      F.orderedCubeSimplex [e] = φ ⁻¹' Set.Icc (0 : ℝ) 1 := by
    exact F.orderedCubeSimplex_singleton_eq_funUnique_preimage_Icc hedges
  have hmap :
      ∫ u in F.orderedCubeSimplex [e], H u
          ∂(volume : Measure (F.EdgeParam → ℝ)) =
        ∫ t in Set.Icc (0 : ℝ) 1, H (φ.symm t) := by
    rw [hsector]
    have hpre :=
      (F.measurePreserving_funUnique_edgeParam_singleton hedges).setIntegral_preimage_emb
        (MeasurableEquiv.measurableEmbedding φ)
        (fun t : ℝ => H (φ.symm t)) (Set.Icc (0 : ℝ) 1)
    have hcongr :
        ∫ u in φ ⁻¹' Set.Icc (0 : ℝ) 1, H u
            ∂(volume : Measure (F.EdgeParam → ℝ)) =
          ∫ u in φ ⁻¹' Set.Icc (0 : ℝ) 1, H (φ.symm (φ u))
            ∂(volume : Measure (F.EdgeParam → ℝ)) := by
      apply setIntegral_congr_fun
      · exact measurableSet_Icc.preimage φ.measurable
      · intro u _hu
        exact congrArg H (φ.left_inv u).symm
    exact hcongr.trans hpre
  calc
    F.orderedContribution [e] ρ
        = ∫ t in Set.Icc (0 : ℝ) 1, H (φ.symm t) := by
          exact F.orderedContribution_singleton_eq_setIntegral_Icc_funUnique
            hedges ρ
    _ = ∫ u in F.orderedCubeSimplex [e], H u
          ∂(volume : Measure (F.EdgeParam → ℝ)) := hmap.symm
    _ = F.orderedCubeSectorContribution [e] ρ := by
          rw [orderedCubeSectorContribution]

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
