/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import LeanPool.BKARForestFormula.BKAR.CubePartition.CubeIntegral

/-! # Almost-everywhere disjointness of the ordered sectors

The measure-theoretic half of the unit-cube partition step: coordinate
collision hyperplanes are Lebesgue-null, distinct ordered sectors meet only
in collisions, hence the sectors are pairwise almost-everywhere disjoint
and the integral of an integrable function over the unit cube is the sum of
its sector integrals.  This justifies folding the per-order sector
integrals of the BKAR forest interpolation formula (see `BKAR.Formula`)
into one cube integral.
-/

noncomputable section

namespace BKAR

namespace OrderedSimplexParams

theorem pairwise_ge :
    ∀ {top : ℝ} {ts : List ℝ},
      OrderedSimplexParams top ts →
        ts.Pairwise fun t s => s ≤ t
  | _, [], _ => by
      exact List.Pairwise.nil
  | _, t :: ts, h => by
      rw [List.pairwise_cons]
      constructor
      · intro s hs
        exact OrderedSimplexParams.le_head_of_mem_tail h hs
      · exact pairwise_ge h.tail

end OrderedSimplexParams

namespace Forest

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordered pairs of distinct forest-edge parameters. -/
def collisionPairs (F : Forest V) : Type _ :=
  {p : F.EdgeParam × F.EdgeParam // p.1 ≠ p.2}

instance (F : Forest V) : Fintype F.collisionPairs := by
  dsimp [collisionPairs]
  infer_instance

/--
The collision locus where two distinct forest-edge cube coordinates agree.
This is the union of the codimension-one hyperplanes that form the overlaps of
the closed ordered sectors.
-/
def collisionSet (F : Forest V) : Set (F.EdgeParam → ℝ) :=
  ⋃ p : F.collisionPairs, {u | u p.val.1 = u p.val.2}

/-- The coordinate-equality hyperplane attached to two distinct edge parameters is null. -/
theorem measure_coordinateCollision_eq_zero
    (F : Forest V) (a b : F.EdgeParam) (hne : a ≠ b) :
    (volume : Measure (F.EdgeParam → ℝ)) {u | u a = u b} = 0 := by
  classical
  let L : (F.EdgeParam → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => u a - u b
      map_add' := by
        intro u v
        simp [Pi.add_apply]
        ring
      map_smul' := by
        intro c u
        simp [Pi.smul_apply, smul_eq_mul, mul_sub] }
  let S : Submodule ℝ (F.EdgeParam → ℝ) := LinearMap.ker L
  have hS_ne_top : S ≠ ⊤ := by
    let v : F.EdgeParam → ℝ := fun e => if e = a then 1 else 0
    have hb : b ≠ a := hne.symm
    have hv_not : v ∉ S := by
      simp [S, L, v, hb]
    intro htop
    exact hv_not (by
      rw [htop]
      exact Submodule.mem_top)
  have hset : (S : Set (F.EdgeParam → ℝ)) = {u | u a = u b} := by
    ext u
    simp [S, L, sub_eq_zero]
  rw [← hset]
  exact Measure.addHaar_submodule volume S hS_ne_top

/-- The full finite collision locus has measure zero. -/
theorem measure_collisionSet_eq_zero (F : Forest V) :
    (volume : Measure (F.EdgeParam → ℝ)) F.collisionSet = 0 := by
  classical
  rw [collisionSet]
  exact measure_iUnion_null fun p =>
    F.measure_coordinateCollision_eq_zero p.val.1 p.val.2 p.property

/--
Auxiliary relation used to compare sector orders. It agrees with descending
parameter order on forest edges and only relates off-forest edges to themselves;
this makes it globally antisymmetric once collisions are excluded.
-/
def sectorOrderRel (F : Forest V) (u : F.EdgeParam → ℝ) :
    Edge V → Edge V → Prop :=
  fun e e' =>
    e = e' ∨
      (e ∈ F.edges ∧ e' ∈ F.edges ∧ F.paramValue u e' ≤ F.paramValue u e)

theorem sectorOrderRel_isAntisymm_of_notMem_collisionSet
    (F : Forest V) {u : F.EdgeParam → ℝ}
    (hno : u ∉ F.collisionSet) :
    Std.Antisymm (F.sectorOrderRel u) := by
  classical
  constructor
  intro e e' hee' he'e
  rcases hee' with heq | hle
  · exact heq
  rcases he'e with heq | hle'
  · exact heq.symm
  by_contra hne
  have hparam : F.paramValue u e = F.paramValue u e' :=
    le_antisymm hle'.2.2 hle.2.2
  have hvalue :
      u ⟨e, hle.1⟩ = u ⟨e', hle.2.1⟩ := by
    simpa [F.paramValue_of_mem u hle.1,
      F.paramValue_of_mem u hle.2.1] using hparam
  exact hno (by
    rw [collisionSet]
    refine Set.mem_iUnion.mpr ⟨⟨(⟨e, hle.1⟩, ⟨e', hle.2.1⟩), ?_⟩, ?_⟩
    · intro hp
      exact hne (congr_arg Subtype.val hp)
    · exact hvalue)

theorem pairwise_sectorOrderRel_of_orderedSimplexParams
    (F : Forest V) (u : F.EdgeParam → ℝ) :
    ∀ (order : List (Edge V)) {top : ℝ},
      (∀ e ∈ order, e ∈ F.edges) →
      OrderedSimplexParams top (order.map (F.paramValue u)) →
      order.Pairwise (F.sectorOrderRel u)
  | [], _, _hmem, _hparams => by
      exact List.Pairwise.nil
  | e :: order, top, hmem, hparams => by
      rw [List.map_cons] at hparams
      rw [List.pairwise_cons]
      constructor
      · intro e' he'
        refine Or.inr ⟨hmem e (by simp), hmem e' (List.mem_cons_of_mem e he'), ?_⟩
        exact OrderedSimplexParams.le_head_of_mem_tail hparams
          (List.mem_map.mpr ⟨e', he', rfl⟩)
      · exact pairwise_sectorOrderRel_of_orderedSimplexParams F u order
          (by
            intro e' he'
            exact hmem e' (List.mem_cons_of_mem e he'))
          hparams.tail

/--
Away from collision hyperplanes, membership in two closed ordered sectors
forces the two canonical edge orders to be equal.
-/
theorem eq_of_mem_orderedCubeSimplex_of_notMem_collisionSet
    (F : Forest V) {order₁ order₂ : List (Edge V)}
    (horder₁ : order₁ ∈ F.edgeOrders) (horder₂ : order₂ ∈ F.edgeOrders)
    {u : F.EdgeParam → ℝ}
    (hno : u ∉ F.collisionSet)
    (hu₁ : u ∈ F.orderedCubeSimplex order₁)
    (hu₂ : u ∈ F.orderedCubeSimplex order₂) :
    order₁ = order₂ := by
  classical
  let r := F.sectorOrderRel u
  have : Std.Antisymm r :=
    F.sectorOrderRel_isAntisymm_of_notMem_collisionSet hno
  have hmem₁ : ∀ e ∈ order₁, e ∈ F.edges := by
    intro e he
    have hset := F.toFinset_eq_of_mem_edgeOrders horder₁
    rw [← hset]
    exact List.mem_toFinset.mpr he
  have hmem₂ : ∀ e ∈ order₂, e ∈ F.edges := by
    intro e he
    have hset := F.toFinset_eq_of_mem_edgeOrders horder₂
    rw [← hset]
    exact List.mem_toFinset.mpr he
  have hpair₁ : order₁.Pairwise r :=
    F.pairwise_sectorOrderRel_of_orderedSimplexParams u order₁ hmem₁ hu₁.2
  have hpair₂ : order₂.Pairwise r :=
    F.pairwise_sectorOrderRel_of_orderedSimplexParams u order₂ hmem₂ hu₂.2
  have hperm : order₁.Perm order₂ :=
    ((F.mem_edgeOrders_iff).mp horder₁).trans
      ((F.mem_edgeOrders_iff).mp horder₂).symm
  exact hperm.eq_of_pairwise' hpair₁ hpair₂

/-- Distinct closed ordered cube sectors only overlap on the collision locus. -/
theorem orderedCubeSimplex_inter_subset_collisionSet_of_ne
    (F : Forest V) {order₁ order₂ : List (Edge V)}
    (horder₁ : order₁ ∈ F.edgeOrders) (horder₂ : order₂ ∈ F.edgeOrders)
    (hne : order₁ ≠ order₂) :
    F.orderedCubeSimplex order₁ ∩ F.orderedCubeSimplex order₂ ⊆
      F.collisionSet := by
  intro u hu
  by_contra hno
  exact hne
    (F.eq_of_mem_orderedCubeSimplex_of_notMem_collisionSet
      horder₁ horder₂ hno hu.1 hu.2)

/-- Distinct canonical ordered cube sectors are a.e. disjoint. -/
theorem aedisjoint_orderedCubeSimplex_of_ne
    (F : Forest V) {order₁ order₂ : List (Edge V)}
    (horder₁ : order₁ ∈ F.edgeOrders) (horder₂ : order₂ ∈ F.edgeOrders)
    (hne : order₁ ≠ order₂) :
    AEDisjoint (volume : Measure (F.EdgeParam → ℝ))
      (F.orderedCubeSimplex order₁) (F.orderedCubeSimplex order₂) := by
  exact measure_mono_null
    (F.orderedCubeSimplex_inter_subset_collisionSet_of_ne horder₁ horder₂ hne)
    F.measure_collisionSet_eq_zero

/-- The canonical ordered cube sectors are pairwise a.e. disjoint. -/
theorem pairwise_aedisjoint_orderedCubeSimplex (F : Forest V) :
    Pairwise
      (fun order₁ order₂ : {order : List (Edge V) // order ∈ F.edgeOrders} =>
        AEDisjoint (volume : Measure (F.EdgeParam → ℝ))
          (F.orderedCubeSimplex order₁.val)
          (F.orderedCubeSimplex order₂.val)) := by
  intro order₁ order₂ hne
  exact F.aedisjoint_orderedCubeSimplex_of_ne
    order₁.property order₂.property
    (fun hval => hne (Subtype.ext hval))

/-- Coordinate lookup as a measurable function on the forest parameter cube. -/
theorem measurable_paramValue (F : Forest V) (e : Edge V) :
    Measurable fun u : F.EdgeParam → ℝ => F.paramValue u e := by
  by_cases he : e ∈ F.edges
  · have hfun :
        (fun u : F.EdgeParam → ℝ => F.paramValue u e) =
          fun u : F.EdgeParam → ℝ => u (⟨e, he⟩ : F.EdgeParam) := by
      funext u
      rw [paramValue, dite_eq_left he]
    rw [hfun]
    exact measurable_pi_apply (⟨e, he⟩ : F.EdgeParam)
  · have hfun :
        (fun u : F.EdgeParam → ℝ => F.paramValue u e) =
          fun _ : F.EdgeParam → ℝ => (1 : ℝ) := by
      funext u
      rw [paramValue, dite_eq_right he]
    rw [hfun]
    exact measurable_const

/-- Measurability of the unit parameter cube. -/
theorem measurableSet_unitCube (F : Forest V) :
    MeasurableSet F.unitCube := by
  rw [unitCube]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- The forest parameter cube is compact. -/
theorem isCompact_unitCube (F : Forest V) :
    IsCompact F.unitCube := by
  rw [unitCube]
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem measurableSet_orderedSimplexParams_map_paramValue
    (F : Forest V) :
    ∀ (order : List (Edge V))
      {topFn : (F.EdgeParam → ℝ) → ℝ},
      Measurable topFn →
      MeasurableSet
        {u : F.EdgeParam → ℝ |
          OrderedSimplexParams (topFn u)
            (order.map (F.paramValue u))}
  | [], _topFn, _htop => by
      simp
  | e :: order, topFn, htop => by
      have hparam : Measurable fun u : F.EdgeParam → ℝ => F.paramValue u e :=
        F.measurable_paramValue e
      simp only [List.map_cons, orderedSimplexParams_cons, Set.ofPred_and]
      simpa [Set.inter_assoc] using
        (((measurableSet_le
              (measurable_const :
                Measurable fun _ : F.EdgeParam → ℝ => (0 : ℝ))
              hparam).inter
            (measurableSet_le hparam htop)).inter
          (measurableSet_orderedSimplexParams_map_paramValue F order hparam))

/-- Each closed ordered cube sector is measurable. -/
theorem measurableSet_orderedCubeSimplex
    (F : Forest V) (order : List (Edge V)) :
    MeasurableSet (F.orderedCubeSimplex order) := by
  rw [orderedCubeSimplex]
  exact F.measurableSet_unitCube.inter
    (F.measurableSet_orderedSimplexParams_map_paramValue order measurable_const)

/--
Almost-disjoint integral partition of the unit cube: once the closed sectors are
measurable and the integrand is integrable on the cube, the integral over the
unit cube is the sum of the sector integrals. The a.e. disjointness comes from
the collision-hyperplane theorem above.
-/
theorem integral_unitCube_eq_tsum_orderedCubeSimplex
    (F : Forest V) (f : (F.EdgeParam → ℝ) → ℝ)
    (hfi : IntegrableOn f F.unitCube
      (volume : Measure (F.EdgeParam → ℝ))) :
    ∫ u in F.unitCube, f u ∂(volume : Measure (F.EdgeParam → ℝ)) =
      ∑' order : {order : List (Edge V) // order ∈ F.edgeOrders},
        ∫ u in F.orderedCubeSimplex order.val, f u
          ∂(volume : Measure (F.EdgeParam → ℝ)) := by
  rw [F.unitCube_eq_iUnion_orderedCubeSimplex]
  exact integral_iUnion_ae
    (fun order =>
      (F.measurableSet_orderedCubeSimplex order.val).nullMeasurableSet)
    F.pairwise_aedisjoint_orderedCubeSimplex
    (by simpa [F.unitCube_eq_iUnion_orderedCubeSimplex] using hfi)

/-- Finite-sum form of `Forest.integral_unitCube_eq_tsum_orderedCubeSimplex`. -/
theorem integral_unitCube_eq_sum_orderedCubeSimplex
    (F : Forest V) (f : (F.EdgeParam → ℝ) → ℝ)
    (hfi : IntegrableOn f F.unitCube
      (volume : Measure (F.EdgeParam → ℝ))) :
    ∫ u in F.unitCube, f u ∂(volume : Measure (F.EdgeParam → ℝ)) =
      Finset.sum
        (Finset.univ :
          Finset {order : List (Edge V) // order ∈ F.edgeOrders})
        (fun order =>
          ∫ u in F.orderedCubeSimplex order.val, f u
            ∂(volume : Measure (F.EdgeParam → ℝ))) := by
  rw [F.integral_unitCube_eq_tsum_orderedCubeSimplex f hfi]
  rw [tsum_fintype]

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
