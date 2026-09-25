/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Singleton

/-! # Ordered coordinate equivalences

For each enumeration of a forest's edge set, constructs the measurable,
measure-preserving equivalence between the forest's edge-parameter space
and `Fin n → ℝ` that reads coordinates in the given order, and defines the
standard ordered simplex `orderedFinSimplex` in `Fin n → ℝ`.  The ordered
cube sector is the preimage of the standard ordered simplex under this
equivalence — the change of variables underlying the simplex-sector
conversion.
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
A canonical edge order lists exactly the same support as the forest edge
parameter subtype.
-/
def edgeParamEquivOrderSubtype
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    {e : Edge V // e ∈ order} ≃ F.EdgeParam where
  toFun e :=
    ⟨e.val, by
      have hset := F.toFinset_eq_of_mem_edgeOrders horder
      rw [← hset]
      exact List.mem_toFinset.mpr e.property⟩
  invFun e :=
    ⟨e.val, by
      have hset := F.toFinset_eq_of_mem_edgeOrders horder
      have he : e.val ∈ order.toFinset := by
        rw [hset]
        exact e.property
      exact List.mem_toFinset.mp he⟩
  left_inv e := by
    exact Subtype.ext rfl
  right_inv e := by
    exact Subtype.ext rfl

/--
The finite coordinate equivalence attached to a canonical edge order.  Its
`i`th coordinate is the `i`th edge in the order.
-/
def edgeParamFinEquivOfOrder
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    Fin order.length ≃ F.EdgeParam :=
  (List.Nodup.getEquiv order (F.nodup_of_mem_edgeOrders horder)).trans
    (F.edgeParamEquivOrderSubtype horder)

@[simp]
theorem edgeParamFinEquivOfOrder_apply_val
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (i : Fin order.length) :
    (F.edgeParamFinEquivOfOrder horder i).val = order.get i := by
  rfl

/--
The measurable equivalence reading forest edge parameters in a canonical
order as ordinary `Fin order.length` coordinates.
-/
def orderMeasurableEquivOfOrder
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    (F.EdgeParam → ℝ) ≃ᵐ (Fin order.length → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
    (F.edgeParamFinEquivOfOrder horder)).symm

theorem measurePreserving_orderMeasurableEquivOfOrder
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    MeasurePreserving (F.orderMeasurableEquivOfOrder horder)
      (volume : Measure (F.EdgeParam → ℝ))
      (volume : Measure (Fin order.length → ℝ)) := by
  let φ : (Fin order.length → ℝ) ≃ᵐ (F.EdgeParam → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder)
  have hφ : MeasurePreserving φ
      (volume : Measure (Fin order.length → ℝ))
      (volume : Measure (F.EdgeParam → ℝ)) :=
    volume_measurePreserving_piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder)
  exact MeasurePreserving.symm φ hφ

/-- The ordered coordinate equivalence is, definitionally, readback along the order equivalence. -/
theorem orderMeasurableEquivOfOrder_apply_edgeParam
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (u : F.EdgeParam → ℝ) (i : Fin order.length) :
    F.orderMeasurableEquivOfOrder horder u i =
      u (F.edgeParamFinEquivOfOrder horder i) := by
  change
    ((MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder)).symm u) i =
        u (F.edgeParamFinEquivOfOrder horder i)
  change
    ((Equiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder)).symm u) i =
        u (F.edgeParamFinEquivOfOrder horder i)
  simp

/-- The ordered coordinate equivalence reads back the parameter of `order.get i`. -/
theorem orderMeasurableEquivOfOrder_apply
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (u : F.EdgeParam → ℝ) (i : Fin order.length) :
    F.orderMeasurableEquivOfOrder horder u i =
      F.paramValue u (order.get i) := by
  have he : order.get i ∈ F.edges := by
    have hset := F.toFinset_eq_of_mem_edgeOrders horder
    rw [← hset]
    exact List.mem_toFinset.mpr (List.get_mem order i)
  change
    ((MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder)).symm u) i =
        F.paramValue u (order.get i)
  change
    ((Equiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder)).symm u) i =
        F.paramValue u (order.get i)
  rw [F.paramValue_of_mem u he]
  rfl

theorem orderMeasurableEquivOfOrder_symm_apply
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ts : Fin order.length → ℝ) (p : F.EdgeParam) :
    (F.orderMeasurableEquivOfOrder horder).symm ts p =
      ts ((F.edgeParamFinEquivOfOrder horder).symm p) := by
  change
    (MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder) ts) p =
        ts ((F.edgeParamFinEquivOfOrder horder).symm p)
  change
    (Equiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder) ts) p =
        ts ((F.edgeParamFinEquivOfOrder horder).symm p)
  rw [Equiv.piCongrLeft_apply]
  simp

/-- The inverse ordered-coordinate equivalence is continuous. -/
theorem continuous_orderMeasurableEquivOfOrder_symm
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    Continuous
      (fun ts : Fin order.length → ℝ =>
        (F.orderMeasurableEquivOfOrder horder).symm ts) := by
  apply continuous_pi
  intro p
  have hfun :
      (fun ts : Fin order.length → ℝ =>
          (F.orderMeasurableEquivOfOrder horder).symm ts p) =
        fun ts : Fin order.length → ℝ =>
          ts ((F.edgeParamFinEquivOfOrder horder).symm p) := by
    funext ts
    exact F.orderMeasurableEquivOfOrder_symm_apply horder ts p
  rw [hfun]
  exact continuous_apply ((F.edgeParamFinEquivOfOrder horder).symm p)

/--
The inverse coordinate equivalence is the same point of the forest cube as
`paramsOfOrder`, when the coordinate list is formed from the `Fin` tuple.
-/
theorem paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ts : Fin order.length → ℝ) :
    F.paramsOfOrder order (List.ofFn ts) =
      (F.orderMeasurableEquivOfOrder horder).symm ts := by
  apply (F.orderMeasurableEquivOfOrder horder).injective
  funext i
  have hmap :
      order.map (F.paramValue (F.paramsOfOrder order (List.ofFn ts))) =
        List.ofFn ts := by
    exact F.map_paramValue_paramsOfOrder_eq_of_mem_edgeOrders horder (by simp)
  have hget := congrArg (fun xs : List ℝ => xs[i.val]?) hmap
  have hcoord :
      F.paramValue (F.paramsOfOrder order (List.ofFn ts)) (order.get i) =
        ts i := by
    have hsome :
        some (F.paramValue (F.paramsOfOrder order (List.ofFn ts)) (order.get i)) =
          some (ts i) := by
      simpa [List.getElem?_map, List.getElem?_ofFn, i.isLt] using hget
    exact Option.some.inj hsome
  calc
    F.orderMeasurableEquivOfOrder horder
        (F.paramsOfOrder order (List.ofFn ts)) i
        = F.paramValue (F.paramsOfOrder order (List.ofFn ts)) (order.get i) := by
          rw [F.orderMeasurableEquivOfOrder_apply horder]
    _ = ts i := hcoord
    _ = F.orderMeasurableEquivOfOrder horder
        ((F.orderMeasurableEquivOfOrder horder).symm ts) i := by
          exact congrFun
            ((F.orderMeasurableEquivOfOrder horder).apply_symm_apply ts).symm i

/--
The ordered finite simplex in `Fin n` coordinates, including the ambient
closed cube bounds.  This is the coordinate target for arbitrary canonical
orders.
-/
def orderedFinSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {ts | (∀ i, 0 ≤ ts i ∧ ts i ≤ 1) ∧
    OrderedSimplexParams 1 (List.ofFn ts)}

theorem mem_orderedFinSimplex_iff {n : ℕ} (ts : Fin n → ℝ) :
    ts ∈ orderedFinSimplex n ↔
      (∀ i, 0 ≤ ts i ∧ ts i ≤ 1) ∧
        OrderedSimplexParams 1 (List.ofFn ts) :=
  Iff.rfl

/-- Reading an arbitrary cube point in canonical order gives the corresponding `ofFn` list. -/
theorem map_paramValue_eq_ofFn_orderMeasurableEquiv
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (u : F.EdgeParam → ℝ) :
    order.map (F.paramValue u) =
      List.ofFn (F.orderMeasurableEquivOfOrder horder u) := by
  apply List.ext_getElem
  · simp
  · intro n hmap hofn
    let i : Fin order.length := ⟨n, by simpa using hmap⟩
    have hread := F.orderMeasurableEquivOfOrder_apply horder u i
    simpa [i, List.getElem_map, List.getElem_ofFn] using hread.symm

/--
Set-level arbitrary-order simplex-sector bridge: a canonical ordered cube
sector is the
preimage of the standard ordered finite simplex under the ordered coordinate
equivalence.
-/
theorem orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    F.orderedCubeSimplex order =
      (F.orderMeasurableEquivOfOrder horder) ⁻¹'
        orderedFinSimplex order.length := by
  ext u
  rw [mem_orderedCubeSimplex_iff]
  change
    u ∈ F.unitCube ∧ OrderedSimplexParams 1 (order.map (F.paramValue u)) ↔
      F.orderMeasurableEquivOfOrder horder u ∈ orderedFinSimplex order.length
  rw [mem_orderedFinSimplex_iff]
  constructor
  · intro h
    constructor
    · intro i
      have hcube := (F.mem_unitCube_iff u).mp h.1
      have hbounds := F.paramValue_mem_Icc u hcube (order.get i)
      simpa [F.orderMeasurableEquivOfOrder_apply horder u i] using hbounds
    · rw [← F.map_paramValue_eq_ofFn_orderMeasurableEquiv horder u]
      exact h.2
  · intro h
    constructor
    · rw [F.mem_unitCube_iff]
      intro p
      let i : Fin order.length := (F.edgeParamFinEquivOfOrder horder).symm p
      have hp : F.edgeParamFinEquivOfOrder horder i = p := by
        dsimp [i]
        exact (F.edgeParamFinEquivOfOrder horder).apply_symm_apply p
      have hread :
          F.orderMeasurableEquivOfOrder horder u i =
            u (F.edgeParamFinEquivOfOrder horder i) :=
        F.orderMeasurableEquivOfOrder_apply_edgeParam horder u i
      have hbounds := h.1 i
      rw [hp] at hread
      simpa [hread] using hbounds
    · rw [F.map_paramValue_eq_ofFn_orderMeasurableEquiv horder u]
      exact h.2

/--
Measure transport for arbitrary canonical orders, for integrands already
written in ordered finite coordinates.
-/
theorem setIntegral_orderedCubeSimplex_orderMeasurableEquiv_eq_orderedFinSimplex
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (g : (Fin order.length → ℝ) → ℝ) :
    ∫ u in F.orderedCubeSimplex order,
        g (F.orderMeasurableEquivOfOrder horder u)
        ∂(volume : Measure (F.EdgeParam → ℝ)) =
      ∫ ts in orderedFinSimplex order.length, g ts := by
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (Fin order.length → ℝ) :=
    F.orderMeasurableEquivOfOrder horder
  have hsector :
      F.orderedCubeSimplex order = φ ⁻¹' orderedFinSimplex order.length := by
    exact F.orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
      horder
  rw [hsector]
  exact (F.measurePreserving_orderMeasurableEquivOfOrder horder).setIntegral_preimage_emb
    (MeasurableEquiv.measurableEmbedding φ) g (orderedFinSimplex order.length)

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
