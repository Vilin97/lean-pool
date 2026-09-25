/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Equiv

/-! # Simplex-sector conversion: two edges

The two-dimensional case of the simplex-sector conversion, in explicit pair
coordinates: the ordered pair sector `{0 ≤ t₂ ≤ t₁ ≤ 1}` in `ℝ × ℝ`, its
identification with the two-edge ordered cube sector through a
measure-preserving pair coordinate equivalence, and the rewriting of both
the cube-sector contribution and the recursive nested contribution in these
coordinates.
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A two-edge canonical order identifies the forest support with that pair. -/
theorem edges_eq_pair_of_pair_mem_edgeOrders
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders) :
    F.edges = ({e₁, e₂} : Finset (Edge V)) := by
  have hset := F.toFinset_eq_of_mem_edgeOrders horder
  simpa using hset.symm

/-- The two entries of a two-edge canonical order are distinct. -/
theorem ne_of_pair_mem_edgeOrders
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders) :
    e₁ ≠ e₂ := by
  have hnodup := F.nodup_of_mem_edgeOrders horder
  simpa using hnodup

theorem edgeParam_eq_left_or_right_of_edges_eq_pair
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V)))
    (p : F.EdgeParam) :
    p.val = e₁ ∨ p.val = e₂ := by
  have hp : p.val ∈ ({e₁, e₂} : Finset (Edge V)) := by
    rw [← hedges]
    exact p.property
  simpa using hp

/--
The coordinate map from a two-edge sector to ordinary pair coordinates, with
the order `[e₁, e₂]`.
-/
def pairCoordOfOrder (F : Forest V) (e₁ e₂ : Edge V)
    (u : F.EdgeParam → ℝ) : ℝ × ℝ :=
  (F.paramValue u e₁, F.paramValue u e₂)

/--
The closed sector in pair coordinates corresponding to
`1 ≥ t₁ ≥ t₂ ≥ 0`.  The redundant upper bound on `t₂` makes this line up
definitionally with the ambient cube constraints.
-/
def orderedPairSector : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1 ∧ z.2 ≤ z.1}

theorem measurableSet_orderedPairSector : MeasurableSet orderedPairSector := by
  have h₁ : MeasurableSet {z : ℝ × ℝ | 0 ≤ z.1} :=
    measurableSet_le measurable_const (measurable_fst : Measurable fun z : ℝ × ℝ => z.1)
  have h₂ : MeasurableSet {z : ℝ × ℝ | z.1 ≤ 1} :=
    measurableSet_le (measurable_fst : Measurable fun z : ℝ × ℝ => z.1) measurable_const
  have h₃ : MeasurableSet {z : ℝ × ℝ | 0 ≤ z.2} :=
    measurableSet_le measurable_const (measurable_snd : Measurable fun z : ℝ × ℝ => z.2)
  have h₄ : MeasurableSet {z : ℝ × ℝ | z.2 ≤ 1} :=
    measurableSet_le (measurable_snd : Measurable fun z : ℝ × ℝ => z.2) measurable_const
  have h₅ : MeasurableSet {z : ℝ × ℝ | z.2 ≤ z.1} :=
    measurableSet_le (measurable_snd : Measurable fun z : ℝ × ℝ => z.2)
      (measurable_fst : Measurable fun z : ℝ × ℝ => z.1)
  change MeasurableSet
    {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1 ∧ z.2 ≤ z.1}
  simpa [Set.inter_def] using h₁.inter (h₂.inter (h₃.inter (h₄.inter h₅)))

omit [Fintype V] [DecidableEq V] in
theorem orderedPairSector_setIntegral_eq_iterated_Icc
    (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f orderedPairSector) :
    ∫ z in orderedPairSector, f z =
      ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc (0 : ℝ) x, f (x, y) := by
  let rect : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)
  have hrect_inter : rect ∩ orderedPairSector = orderedPairSector := by
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      exact ⟨⟨⟨hz.1, hz.2.1⟩, trivial⟩, hz⟩
  have hind :
      IntegrableOn (orderedPairSector.indicator f) rect
        (volume : Measure (ℝ × ℝ)) :=
    (hf.integrable_indicator measurableSet_orderedPairSector).integrableOn
  calc
    ∫ z in orderedPairSector, f z
        = ∫ z in rect, orderedPairSector.indicator f z := by
          rw [setIntegral_indicator measurableSet_orderedPairSector]
          rw [hrect_inter]
    _ = ∫ x in Set.Icc (0 : ℝ) 1,
          ∫ y in (Set.univ : Set ℝ), orderedPairSector.indicator f (x, y) := by
          exact setIntegral_prod (orderedPairSector.indicator f) hind
    _ = ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc (0 : ℝ) x, f (x, y) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro x hx
          have hfiber :
              (fun y : ℝ => orderedPairSector.indicator f (x, y)) =
                (Set.Icc (0 : ℝ) x).indicator (fun y : ℝ => f (x, y)) := by
            funext y
            have hmem : (x, y) ∈ orderedPairSector ↔ y ∈ Set.Icc (0 : ℝ) x := by
              constructor
              · intro hy
                exact ⟨hy.2.2.1, hy.2.2.2.2⟩
              · intro hy
                exact ⟨hx.1, hx.2, hy.1, hy.2.trans hx.2, hy.2⟩
            by_cases hy : y ∈ Set.Icc (0 : ℝ) x
            · have hsector : (x, y) ∈ orderedPairSector := hmem.mpr hy
              simp [Set.indicator_of_mem hsector, Set.indicator_of_mem hy]
            · have hsector : (x, y) ∉ orderedPairSector := by
                intro h
                exact hy (hmem.mp h)
              simp [Set.indicator_of_notMem hsector, Set.indicator_of_notMem hy]
          change (∫ y in (Set.univ : Set ℝ),
              orderedPairSector.indicator f (x, y)) =
            ∫ y in Set.Icc (0 : ℝ) x, f (x, y)
          rw [setIntegral_univ, hfiber, integral_indicator measurableSet_Icc]

omit [Fintype V] [DecidableEq V] in
theorem orderedPairSector_setIntegral_eq_iterated_interval
    (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f orderedPairSector) :
    ∫ z in orderedPairSector, f z =
      ∫ x in 0..(1 : ℝ), ∫ y in 0..x, f (x, y) := by
  calc
    ∫ z in orderedPairSector, f z
        = ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc (0 : ℝ) x, f (x, y) := by
          exact orderedPairSector_setIntegral_eq_iterated_Icc f hf
    _ = ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in 0..x, f (x, y) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro x hx
          change (∫ y in Set.Icc (0 : ℝ) x, f (x, y)) =
            ∫ y in 0..x, f (x, y)
          rw [intervalIntegral.integral_of_le hx.1]
          rw [setIntegral_congr_set Ioc_ae_eq_Icc]
    _ = ∫ x in 0..(1 : ℝ), ∫ y in 0..x, f (x, y) := by
          rw [intervalIntegral.integral_of_le zero_le_one]
          rw [setIntegral_congr_set Ioc_ae_eq_Icc]

/--
When the forest support is exactly `{e₁, e₂}`, its edge-parameter subtype is
canonically equivalent to `Fin 2` in the order `[e₁, e₂]`.
-/
def edgeParamFinTwoEquivOfPair
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂) :
    Fin 2 ≃ F.EdgeParam where
  toFun i :=
    if i = 0 then
      ⟨e₁, by
        rw [hedges]
        exact Finset.mem_insert_self e₁ {e₂}⟩
    else
      ⟨e₂, by
        rw [hedges]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂)⟩
  invFun p := if p.val = e₁ then 0 else 1
  left_inv := by
    intro i
    fin_cases i <;> simp [hne.symm]
  right_inv := by
    intro p
    have he₁ : e₁ ∈ F.edges := by
      rw [hedges]
      exact Finset.mem_insert_self e₁ {e₂}
    have he₂ : e₂ ∈ F.edges := by
      rw [hedges]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂)
    rcases F.edgeParam_eq_left_or_right_of_edges_eq_pair hedges p with hp | hp
    · have hp_eq : p = ⟨e₁, he₁⟩ := Subtype.ext hp
      simp [hp_eq]
    · have hp_eq : p = ⟨e₂, he₂⟩ := Subtype.ext hp
      simp [hp_eq, hne.symm]

/--
The measure-space equivalence sending the two forest parameters, in order, to
ordinary pair coordinates.
-/
def pairMeasurableEquivOfPair
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂) :
    (F.EdgeParam → ℝ) ≃ᵐ (ℝ × ℝ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
    (F.edgeParamFinTwoEquivOfPair hedges hne)).symm).trans
      (@MeasurableEquiv.finTwoArrow ℝ _)

theorem pairMeasurableEquivOfPair_apply
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂)
    (u : F.EdgeParam → ℝ) :
    F.pairMeasurableEquivOfPair hedges hne u =
      F.pairCoordOfOrder e₁ e₂ u := by
  have he₁ : e₁ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_self e₁ {e₂}
  have he₂ : e₂ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂)
  ext
  · simp only [pairMeasurableEquivOfPair, pairCoordOfOrder,
      MeasurableEquiv.trans_apply]
    rw [F.paramValue_of_mem u he₁]
    change ((MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
        (F.edgeParamFinTwoEquivOfPair hedges hne)).symm u) 0 =
      u ⟨e₁, he₁⟩
    change ((Equiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
        (F.edgeParamFinTwoEquivOfPair hedges hne)).symm u) 0 =
      u ⟨e₁, he₁⟩
    simp [edgeParamFinTwoEquivOfPair]
  · simp only [pairMeasurableEquivOfPair, pairCoordOfOrder,
      MeasurableEquiv.trans_apply]
    rw [F.paramValue_of_mem u he₂]
    change ((MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
        (F.edgeParamFinTwoEquivOfPair hedges hne)).symm u) 1 =
      u ⟨e₂, he₂⟩
    change ((Equiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
        (F.edgeParamFinTwoEquivOfPair hedges hne)).symm u) 1 =
      u ⟨e₂, he₂⟩
    simp [edgeParamFinTwoEquivOfPair]

theorem measurePreserving_pairMeasurableEquivOfPair
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂) :
    MeasurePreserving (F.pairMeasurableEquivOfPair hedges hne)
      (volume : Measure (F.EdgeParam → ℝ)) (volume : Measure (ℝ × ℝ)) := by
  let φ₀ : (Fin 2 → ℝ) ≃ᵐ (F.EdgeParam → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinTwoEquivOfPair hedges hne)
  have hφ₀ : MeasurePreserving φ₀
      (volume : Measure (Fin 2 → ℝ)) (volume : Measure (F.EdgeParam → ℝ)) :=
    volume_measurePreserving_piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinTwoEquivOfPair hedges hne)
  have hφ₀symm : MeasurePreserving φ₀.symm
      (volume : Measure (F.EdgeParam → ℝ)) (volume : Measure (Fin 2 → ℝ)) :=
    MeasurePreserving.symm φ₀ hφ₀
  have hpair : MeasurePreserving (@MeasurableEquiv.finTwoArrow ℝ _)
      (volume : Measure (Fin 2 → ℝ)) (volume : Measure (ℝ × ℝ)) :=
    volume_preserving_finTwoArrow ℝ
  simpa [pairMeasurableEquivOfPair, φ₀, Function.comp_def] using! hpair.comp hφ₀symm

theorem pairCoordOfOrder_pairMeasurableEquivOfPair_symm
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂)
    (z : ℝ × ℝ) :
    F.pairCoordOfOrder e₁ e₂
        ((F.pairMeasurableEquivOfPair hedges hne).symm z) = z := by
  rw [← F.pairMeasurableEquivOfPair_apply hedges hne
    ((F.pairMeasurableEquivOfPair hedges hne).symm z)]
  exact (F.pairMeasurableEquivOfPair hedges hne).apply_symm_apply z

theorem paramsOfOrder_pair_eq_pairMeasurableEquivOfPair_symm
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂)
    (z : ℝ × ℝ) :
    F.paramsOfOrder [e₁, e₂] [z.1, z.2] =
      (F.pairMeasurableEquivOfPair hedges hne).symm z := by
  have he₁ : e₁ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_self e₁ {e₂}
  have he₂ : e₂ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂)
  have hcoord := F.pairCoordOfOrder_pairMeasurableEquivOfPair_symm hedges hne z
  have hleft :
      ((F.pairMeasurableEquivOfPair hedges hne).symm z) ⟨e₁, he₁⟩ = z.1 := by
    have hfst := congrArg Prod.fst hcoord
    simpa [pairCoordOfOrder, F.paramValue_of_mem _ he₁] using hfst
  have hright :
      ((F.pairMeasurableEquivOfPair hedges hne).symm z) ⟨e₂, he₂⟩ = z.2 := by
    have hsnd := congrArg Prod.snd hcoord
    simpa [pairCoordOfOrder, F.paramValue_of_mem _ he₂] using hsnd
  funext p
  rcases F.edgeParam_eq_left_or_right_of_edges_eq_pair hedges p with hp | hp
  · have hp_eq : p = ⟨e₁, he₁⟩ := Subtype.ext hp
    rw [hp_eq]
    rw [F.paramsOfOrder_cons_self e₁ [e₂] z.1 [z.2] he₁]
    exact hleft.symm
  · have hp_eq : p = ⟨e₂, he₂⟩ := Subtype.ext hp
    rw [hp_eq]
    rw [F.paramsOfOrder_cons_of_ne [e₂] z.1 [z.2] he₂ hne.symm]
    simpa using hright.symm

theorem unitCube_iff_pair_bounds_of_edges_eq_pair
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V)))
    (u : F.EdgeParam → ℝ) :
    u ∈ F.unitCube ↔
      0 ≤ F.paramValue u e₁ ∧ F.paramValue u e₁ ≤ 1 ∧
        0 ≤ F.paramValue u e₂ ∧ F.paramValue u e₂ ≤ 1 := by
  have he₁ : e₁ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_self e₁ {e₂}
  have he₂ : e₂ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂)
  constructor
  · intro hu
    have hcube := (F.mem_unitCube_iff u).mp hu
    exact ⟨(F.paramValue_mem_Icc u hcube e₁).1,
      (F.paramValue_mem_Icc u hcube e₁).2,
      (F.paramValue_mem_Icc u hcube e₂).1,
      (F.paramValue_mem_Icc u hcube e₂).2⟩
  · intro hbounds
    rw [F.mem_unitCube_iff]
    intro p
    rcases F.edgeParam_eq_left_or_right_of_edges_eq_pair hedges p with hp | hp
    · have hp_eq : p = ⟨e₁, he₁⟩ := Subtype.ext hp
      rw [hp_eq]
      have hpair :
          0 ≤ F.paramValue u e₁ ∧ F.paramValue u e₁ ≤ 1 :=
        ⟨hbounds.1, hbounds.2.1⟩
      simpa [F.paramValue_of_mem u he₁] using hpair
    · have hp_eq : p = ⟨e₂, he₂⟩ := Subtype.ext hp
      rw [hp_eq]
      have hpair :
          0 ≤ F.paramValue u e₂ ∧ F.paramValue u e₂ ≤ 1 :=
        ⟨hbounds.2.2.1, hbounds.2.2.2⟩
      simpa [F.paramValue_of_mem u he₂] using hpair

theorem orderedCubeSimplex_pair_eq_pairCoord_preimage_orderedPairSector
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders) :
    F.orderedCubeSimplex [e₁, e₂] =
      (F.pairCoordOfOrder e₁ e₂) ⁻¹' orderedPairSector := by
  let hedges := F.edges_eq_pair_of_pair_mem_edgeOrders horder
  ext u
  rw [mem_orderedCubeSimplex_iff]
  have hunit := F.unitCube_iff_pair_bounds_of_edges_eq_pair hedges u
  constructor
  · intro h
    have hbounds := hunit.mp h.1
    have hsimplex := h.2
    simp only [List.map_cons, List.map_nil, orderedSimplexParams_cons,
      orderedSimplexParams_nil, and_true] at hsimplex
    exact ⟨hbounds.1, hbounds.2.1, hbounds.2.2.1, hbounds.2.2.2,
      hsimplex.2.2.2⟩
  · intro h
    constructor
    · exact hunit.mpr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
    · simp only [List.map_cons, List.map_nil, orderedSimplexParams_cons,
        orderedSimplexParams_nil, and_true]
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

theorem orderedCubeSimplex_pair_eq_pairMeasurableEquiv_preimage_orderedPairSector
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders) :
    F.orderedCubeSimplex [e₁, e₂] =
      (F.pairMeasurableEquivOfPair
        (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
        (F.ne_of_pair_mem_edgeOrders horder)) ⁻¹' orderedPairSector := by
  rw [F.orderedCubeSimplex_pair_eq_pairCoord_preimage_orderedPairSector horder]
  ext u
  simp only [Set.mem_preimage]
  rw [F.pairMeasurableEquivOfPair_apply
    (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
    (F.ne_of_pair_mem_edgeOrders horder) u]

/--
Two-edge simplex-sector coordinate transport: integrating over the ordered
cube sector is
the same as integrating over the explicit pair-coordinate sector, with the
integrand pulled back by the inverse coordinate equivalence.
-/
theorem setIntegral_orderedCubeSimplex_pair_eq_orderedPairSector
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (g : (F.EdgeParam → ℝ) → ℝ) :
    ∫ u in F.orderedCubeSimplex [e₁, e₂], g u
        ∂(volume : Measure (F.EdgeParam → ℝ)) =
      ∫ z in orderedPairSector,
        g ((F.pairMeasurableEquivOfPair
          (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
          (F.ne_of_pair_mem_edgeOrders horder)).symm z) := by
  let hedges := F.edges_eq_pair_of_pair_mem_edgeOrders horder
  let hne := F.ne_of_pair_mem_edgeOrders horder
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (ℝ × ℝ) :=
    F.pairMeasurableEquivOfPair hedges hne
  have hsector :
      F.orderedCubeSimplex [e₁, e₂] = φ ⁻¹' orderedPairSector := by
    exact F.orderedCubeSimplex_pair_eq_pairMeasurableEquiv_preimage_orderedPairSector
      horder
  rw [hsector]
  have hpre :=
    (F.measurePreserving_pairMeasurableEquivOfPair hedges hne).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding φ)
      (fun z : ℝ × ℝ => g (φ.symm z)) orderedPairSector
  have hcongr :
      ∫ u in φ ⁻¹' orderedPairSector, g u
          ∂(volume : Measure (F.EdgeParam → ℝ)) =
        ∫ u in φ ⁻¹' orderedPairSector, g (φ.symm (φ u))
          ∂(volume : Measure (F.EdgeParam → ℝ)) := by
    apply setIntegral_congr_fun
    · exact measurableSet_orderedPairSector.preimage φ.measurable
    · intro u _hu
      exact congrArg g (φ.left_inv u).symm
  exact hcongr.trans hpre

/--
The two-edge ordered cube contribution, rewritten in explicit pair
coordinates. This is the sector-side half of the two-dimensional
simplex-sector bridge.
-/
theorem orderedCubeSectorContribution_pair_eq_orderedPairSectorIntegral
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedCubeSectorContribution [e₁, e₂] ρ =
      ∫ z in orderedPairSector,
        mixedPartialList [e₁, e₂].reverse ρ
          (F.standardInterp
            ((F.pairMeasurableEquivOfPair
              (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
              (F.ne_of_pair_mem_edgeOrders horder)).symm z)) := by
  rw [orderedCubeSectorContribution]
  exact F.setIntegral_orderedCubeSimplex_pair_eq_orderedPairSector horder
    (fun u => mixedPartialList [e₁, e₂].reverse ρ (F.standardInterp u))

/--
The two-edge recursive ordered contribution in the same explicit pair
coordinates as the cube-sector contribution. The remaining conversion step is the
ordinary triangular-domain integral theorem connecting this nested integral to
the set integral over `orderedPairSector`.
-/
theorem orderedContribution_pair_eq_nested_pairMeasurableEquivIntegral
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedContribution [e₁, e₂] ρ =
      ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁,
        mixedPartialList [e₁, e₂].reverse ρ
          (F.standardInterp
            ((F.pairMeasurableEquivOfPair
              (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
              (F.ne_of_pair_mem_edgeOrders horder)).symm (t₁, t₂))) := by
  let hedges := F.edges_eq_pair_of_pair_mem_edgeOrders horder
  let hne := F.ne_of_pair_mem_edgeOrders horder
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (ℝ × ℝ) :=
    F.pairMeasurableEquivOfPair hedges hne
  let H : (F.EdgeParam → ℝ) → ℝ :=
    fun u => mixedPartialList [e₁, e₂].reverse ρ (F.standardInterp u)
  calc
    F.orderedContribution [e₁, e₂] ρ
        = ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁,
            H (F.paramsOfOrder [e₁, e₂] [t₁, t₂]) := by
          rw [orderedContribution, orderedSimplexIntegral_pair]
    _ = ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁,
            H (φ.symm (t₁, t₂)) := by
          apply intervalIntegral.integral_congr
          intro t₁ _ht₁
          apply intervalIntegral.integral_congr
          intro t₂ _ht₂
          change H (F.paramsOfOrder [e₁, e₂] [t₁, t₂]) =
            H (φ.symm (t₁, t₂))
          rw [F.paramsOfOrder_pair_eq_pairMeasurableEquivOfPair_symm hedges hne
            (t₁, t₂)]
    _ = ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁,
        mixedPartialList [e₁, e₂].reverse ρ
          (F.standardInterp (φ.symm (t₁, t₂))) := rfl

theorem integrableOn_orderedPairSector_pairIntegrand
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    IntegrableOn
      (fun z : ℝ × ℝ =>
        mixedPartialList [e₁, e₂].reverse ρ
          (F.standardInterp
            ((F.pairMeasurableEquivOfPair
              (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
              (F.ne_of_pair_mem_edgeOrders horder)).symm z)))
      orderedPairSector := by
  let hedges := F.edges_eq_pair_of_pair_mem_edgeOrders horder
  let hne := F.ne_of_pair_mem_edgeOrders horder
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (ℝ × ℝ) :=
    F.pairMeasurableEquivOfPair hedges hne
  let H : (F.EdgeParam → ℝ) → ℝ :=
    fun u => mixedPartialList [e₁, e₂].reverse ρ (F.standardInterp u)
  have hsector :
      F.orderedCubeSimplex [e₁, e₂] = φ ⁻¹' orderedPairSector := by
    exact F.orderedCubeSimplex_pair_eq_pairMeasurableEquiv_preimage_orderedPairSector
      horder
  have hH_unit : IntegrableOn H F.unitCube :=
    F.integrableOn_orderedCubeSectorIntegrand [e₁, e₂] ρ hρ
  have hH_pre : IntegrableOn H (φ ⁻¹' orderedPairSector) := by
    rw [← hsector]
    exact hH_unit.mono_set (F.orderedCubeSimplex_subset_unitCube [e₁, e₂])
  have hcomp :
      IntegrableOn ((fun z : ℝ × ℝ => H (φ.symm z)) ∘ φ)
        (φ ⁻¹' orderedPairSector) := by
    refine hH_pre.congr_fun ?_ (measurableSet_orderedPairSector.preimage φ.measurable)
    intro u _hu
    exact congrArg H (φ.left_inv u).symm
  exact
    ((F.measurePreserving_pairMeasurableEquivOfPair hedges hne).integrableOn_comp_preimage
      (MeasurableEquiv.measurableEmbedding φ)
      (f := fun z : ℝ × ℝ => H (φ.symm z))
      (s := orderedPairSector)).mp hcomp

theorem orderedContribution_pair_eq_orderedCubeSectorContribution
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    F.orderedContribution [e₁, e₂] ρ =
      F.orderedCubeSectorContribution [e₁, e₂] ρ := by
  let pairIntegrand : ℝ × ℝ → ℝ :=
    fun z =>
      mixedPartialList [e₁, e₂].reverse ρ
        (F.standardInterp
          ((F.pairMeasurableEquivOfPair
            (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
            (F.ne_of_pair_mem_edgeOrders horder)).symm z))
  have hint : IntegrableOn pairIntegrand orderedPairSector :=
    F.integrableOn_orderedPairSector_pairIntegrand horder ρ hρ
  calc
    F.orderedContribution [e₁, e₂] ρ
        = ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁, pairIntegrand (t₁, t₂) := by
          exact F.orderedContribution_pair_eq_nested_pairMeasurableEquivIntegral
            horder ρ
    _ = ∫ z in orderedPairSector, pairIntegrand z := by
          exact (orderedPairSector_setIntegral_eq_iterated_interval pairIntegrand hint).symm
    _ = F.orderedCubeSectorContribution [e₁, e₂] ρ := by
          exact (F.orderedCubeSectorContribution_pair_eq_orderedPairSectorIntegral
            horder ρ).symm


end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
