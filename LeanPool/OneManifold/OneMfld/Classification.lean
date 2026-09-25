/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic
public import LeanPool.OneManifold.OneMfld.UnitInterval
public import LeanPool.OneManifold.OneMfld.FiniteIntervalCharts
public import LeanPool.OneManifold.OneMfld.IntervalCharts
public import LeanPool.OneManifold.OneMfld.NiceCharts
public import LeanPool.OneManifold.OneMfld.ClassifyOverlaps
public import LeanPool.OneManifold.OneMfld.Compactness


/-!
# Classification

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

variable
  {M : Type*}
  [TopologicalSpace M]
  [ConnectedSpace M]

/-- Remove a chart whose source is contained in another chart, reducing the atlas size. -/
noncomputable def subsumeCharts (ht : FinitelyIntervalChartedSpace M)
  {a : OpenPartialHomeomorph M NNReal} (ha : a ∈ ht.atlas)
  {b : OpenPartialHomeomorph M NNReal} (hb : b ∈ ht.atlas)
  (hs : a.source ⊆ b.source) (hab : a ≠ b) :
  { ht' : FinitelyIntervalChartedSpace M | Nat.card ht'.atlas = Nat.card ht.atlas - 1 } := by
    let ht' : FinitelyIntervalChartedSpace M :=
    { chartAt := by
        intro x
        by_cases h : a = ht.chartAt x
        · exact b
        · exact ht.chartAt x
    , atlas := ht.atlas \ { a }
    , chart_mem_atlas := by
        intro x
        split_ifs with h
        · apply Set.mem_sdiff_singleton.mpr
          apply And.intro
          · exact hb
          · exact id (Ne.symm hab)
        · apply Set.mem_sdiff_singleton.mpr
          apply And.intro
          · exact ChartedSpace.chart_mem_atlas x
          · exact fun a_1 => h (id (Eq.symm a_1))
    , mem_chart_source := by
        intro x
        split_ifs with h
        · rw [h] at hs
          apply hs
          exact ChartedSpace.mem_chart_source x
        · exact ChartedSpace.mem_chart_source x
    , is_finite := Set.Finite.subset ht.is_finite Set.sdiff_subset
    , is_interval := by
        intro φ hφ
        apply ht.is_interval
        exact Set.mem_of_mem_sdiff hφ
    }
    use ht'
    exact Set.ncard_sdiff_singleton_of_mem ha


/-- Replace two overlapping charts by a chart on their union, reducing the atlas size. -/
noncomputable def replaceCharts (ht : FinitelyIntervalChartedSpace M)
  {a : OpenPartialHomeomorph M NNReal} (ha : a ∈ ht.atlas)
  {b : OpenPartialHomeomorph M NNReal} (hb : b ∈ ht.atlas)
  (ho : Overlap a.source b.source)
  (f : IChart M) (hf : f.source = a.source ∪ b.source) :
  { ht' : FinitelyIntervalChartedSpace M | Nat.card ht'.atlas ≤ Nat.card ht.atlas - 1 } := by
    let hab : a ≠ b := by
      by_contra hab
      rw [hab] at ho
      let ho1 := ho.2.1
      simp only [sdiff_self, Set.bot_eq_empty, Set.not_nonempty_empty] at ho1
    let ht' : FinitelyIntervalChartedSpace M :=
    { chartAt := by
        intro x
        by_cases h : a = ht.chartAt x
        · exact f.toOpenPartialHomeomorph
        · by_cases h : b = ht.chartAt x
          · exact f.toOpenPartialHomeomorph
          · exact ht.chartAt x
    , atlas := (ht.atlas \ { a, b }) ∪ ({ f.toOpenPartialHomeomorph } : Set _)
    , chart_mem_atlas := by
        intro x
        split_ifs with h h'
        · simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff,
          not_or, true_or]
        · simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff,
          not_or, true_or]
        · simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_sdiff, chart_mem_atlas,
          Set.mem_singleton_iff, not_or, true_and]
          right
          exact ⟨fun a_1 => h (id (Eq.symm a_1)), fun a => h' (id (Eq.symm a))⟩
    , mem_chart_source := by
        intro x
        split_ifs with h h'
        · rw [hf]
          simp only [Set.mem_union]
          left
          rw [h]
          exact ChartedSpace.mem_chart_source x
        · rw [hf]
          simp only [Set.mem_union]
          right
          rw [h']
          exact ChartedSpace.mem_chart_source x
        · exact ChartedSpace.mem_chart_source x
    , is_finite := by
        have : Finite ht.atlas := ht.is_finite
        simp only [Set.union_singleton]
        exact Finite.Set.finite_insert f.toOpenPartialHomeomorph (ChartedSpace.atlas \ {a, b})
    , is_interval := by
        intro x hx
        simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff,
          not_or] at hx
        rcases hx with (hx|hx)
        · rw [hx]
          apply f.is_interval
        · apply ht.is_interval
          exact hx.1
    }
    use ht'
    have pair : ( { a, b } : Set (OpenPartialHomeomorph M NNReal) ).ncard = 2 := Set.ncard_pair hab
    have equal : ht.atlas \ {a, b} ∪ {a, b} = ht.atlas := Set.sdiff_union_of_subset
        (Set.pair_subset ha hb)
    have union : ((ht.atlas \ { a, b } : Set _) ∪ {a, b} : Set _).ncard = (ht.atlas \ { a, b } :
        Set _).ncard + ( { a, b } : Set _ ).ncard := by
      apply Set.ncard_union_eq
      · exact Set.disjoint_sdiff_left
      · apply Set.Finite.sdiff
        exact ht.is_finite
      exact Set.toFinite {a, b}
    rw [pair] at union
    rw [equal] at union
    dsimp [ht']
    have : (ht.atlas \ { a, b } : Set _).ncard = (ht.atlas).ncard - 2 := by
      rw [union]
      exact rfl
    have t : (ht.atlas \ {a, b} ∪ {f.toOpenPartialHomeomorph}).ncard ≤ (ht.atlas \ { a, b } :
        Set _).ncard + ({f.toOpenPartialHomeomorph} : Set _).ncard := by
      apply Set.ncard_union_le
    rw [this] at t
    simp only [Set.ncard_singleton] at t
    have t' : ht.atlas.ncard - 2 + 1 ≤ ht.atlas.ncard - 1 := by
      have nonzero : ht.atlas.ncard ≥ 2 := by
        rw [←pair]
        apply Set.ncard_le_ncard
        · exact Set.pair_subset ha hb
        exact ht.is_finite
      ring_nf
      apply Nat.one_add_le_iff.mpr
      exact Nat.sub_succ_lt_self ht.atlas.ncard 1 nonzero
    exact Nat.le_trans t t'

lemma nonempty_atlas (ht : FinitelyIntervalChartedSpace M) : ht.atlas.Nonempty := by
  by_contra nonempty
  have he : Nonempty M := ConnectedSpace.toNonempty
  have x := he.some
  let chart := ht.chartAt x
  have hc : chart ∈ ht.atlas := ht.chart_mem_atlas x
  exfalso
  exact nonempty (Set.nonempty_of_mem hc)

lemma more_than_one_chart [CompactSpace M] (ht : FinitelyIntervalChartedSpace M) : Nat.card
    ht.atlas > 1 := by
  have z := (ConnectedSpace.toNonempty : Nonempty M).some
  let φ := ht.chartAt z
  have nonempty := nonempty_atlas ht
  have hzero : Nat.card ht.atlas > 0 := by
    refine (Set.natCard_pos ?_).mpr nonempty
    exact ht.is_finite
  by_contra htwo
  have hone : Nat.card ht.atlas = 1 := by linarith
  have he : ∃ (a : OpenPartialHomeomorph M NNReal), ht.atlas = { a } := Set.ncard_eq_one.mp hone
  rcases he with ⟨a,ha⟩
  have : φ ∈ ht.atlas := ChartedSpace.chart_mem_atlas z
  rw [ha] at this
  have hφa : φ = a := by exact this
  have h : a.source = Set.univ := by
    ext x
    apply Iff.intro
    · exact fun _ => trivial
    · intro hx
      let c := ht.chartAt x
      have : c ∈ ht.atlas := ht.chart_mem_atlas x
      have : c = a := by
        rw [ha] at this
        exact this
      rw [←this]
      exact ht.mem_chart_source x
  -- a.source is homeo to a.target which is not compact
  have notcompactφ : ¬ CompactSpace (φ.target) := by
    apply noncompact_target
    · exact ChartedSpace.chart_mem_atlas z
    exact ChartedSpace.mem_chart_source z
  have notcompact : ¬ CompactSpace (a.target) := by
    rwa [←hφa]
  exfalso
  apply notcompact
  refine isCompact_iff_compactSpace.mp ?_
  have : a.target = a.toFun '' a.source := Eq.symm (PartialEquiv.image_source_eq_target
      a.toPartialEquiv)
  rw [this]
  apply IsCompact.image_of_continuousOn
  · rw [h]
    exact CompactSpace.isCompact_univ
  · exact a.continuousOn_toFun

lemma find_overlap [CompactSpace M] (ht : FinitelyIntervalChartedSpace M) {a :
    OpenPartialHomeomorph M NNReal}
  (ha : a ∈ ht.atlas) {x : M} (hx : x ∈ a.source)
  (contains : ∀ c ∈ ChartedSpace.atlas \ {a}, ¬ a.source ⊆ c.source) :
  ∃ (b : OpenPartialHomeomorph M NNReal), (b ∈ ht.atlas \ {a}) ∧ (Overlap a.source b.source) := by
    by_contra h
    push Not at h
    have ho : IsOpen a.source := a.open_source
    have hc : IsClosed a.source := by
      have comp : a.sourceᶜ = ⋃ (b ∈ { c ∈ ChartedSpace.atlas \ {a} | ¬ (c.source ⊆ a.source)
          }), b.source := by
        ext z
        apply Iff.intro
        · intro hz
          simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_iUnion,
            exists_prop]
          use ChartedSpace.chartAt z
          simp only [chart_mem_atlas, true_and, mem_chart_source, and_true]
          by_contra hza
          push Not at hza
          apply hz
          apply hza
          · by_contra hc
            rw [←hc] at hz
            simp only [Set.mem_compl_iff, mem_chart_source, not_true_eq_false] at hz
          exact ChartedSpace.mem_chart_source z
        · intro hz
          simp only [Set.mem_compl_iff]
          by_contra hza
          simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_iUnion, exists_prop] at hz
          rcases hz with ⟨ i, ⟨ ⟨ hia, hia' ⟩, his ⟩, hzi ⟩
          specialize h i
          have hic : i ∈ ChartedSpace.atlas \ {a} := Set.mem_sdiff_of_mem hia hia'
          specialize h hic
          apply h
          apply does_overlap
          · use z
            simp only [Set.mem_inter_iff]
            tauto
          · exact contains i hic
          · exact his
      refine { isOpen_compl := ?_ }
      rw [comp]
      apply isOpen_biUnion
      exact fun i a => i.open_source
    have hco : IsClopen a.source := ⟨hc, ho⟩
    have he : IsPreconnected (Set.univ : Set M) := isPreconnected_univ
    have he' := he.subset_isClopen hco
    have hn : (Set.univ ∩ a.source).Nonempty := by
      apply Set.inter_nonempty.mpr
      use x
      exact (Set.mem_ite_empty_right (x ∈ Set.univ) a.source x).mp hx
    have h' := he' hn
    have hs : a.source ⊆ Set.univ := by exact fun ⦃a_1⦄ a => trivial
    have he : a.source = Set.univ := Set.eq_univ_of_univ_subset (he' hn)
    have hcpct : ¬ CompactSpace a.target := by
      apply noncompact_target
      · exact ha
      exact hx
    apply hcpct
    refine isCompact_iff_compactSpace.mp ?_
    have : a.target = a.toFun '' a.source := Eq.symm (PartialEquiv.image_source_eq_target
        a.toPartialEquiv)
    rw [this]
    rw [he]
    have hcpctM : IsCompact (Set.univ : Set M) := CompactSpace.isCompact_univ
    refine IsCompact.image_of_continuousOn hcpctM ?_
    rw [←he]
    exact a.continuousOn_toFun

/-- Classify a compact connected Hausdorff one-manifold using induction on a finite interval
atlas. -/
noncomputable def classification' [T2Space M] [CompactSpace M] (ht :
    FinitelyIntervalChartedSpace M) : (Homeomorph M Circle) ⊕ (Homeomorph M UnitInterval) := by
    -- instead, use the fact that M is nonempty and then use chartat
    have x := (ConnectedSpace.toNonempty : Nonempty M).some
    let φ := ht.chartAt x
    have nonempty := nonempty_atlas ht
    --let φ := nonempty.some
    by_cases nonempty' : (ht.atlas \ {φ}).Nonempty
    · by_cases contains : ∃ (ψ : OpenPartialHomeomorph M NNReal), (ψ ∈ ht.atlas \ {φ}) ∧
        (φ.source ⊆ ψ.source)
      · let ψ := contains.choose
        let hψ := contains.choose_spec
        have hψ' : ψ ∈ ht.atlas := by
          have : ht.atlas \ { φ } ⊆ ht.atlas := Set.sdiff_subset
          apply this
          exact hψ.1
        have : φ.source ⊆ ψ.source := hψ.2
        have hd : φ ≠ ψ := by
          have : ψ ∈ ChartedSpace.atlas \ {φ} := hψ.1
          by_contra hd
          rw [←hd] at this
          have this' : φ ∉ ChartedSpace.atlas \ {φ} := by exact Set.notMem_sdiff_of_mem rfl
          exact this' this
        have ⟨ ht', ht'' ⟩ := subsumeCharts ht (ChartedSpace.chart_mem_atlas x) hψ' this hd
        exact classification' ht'
      · have : ∃ (ψ : OpenPartialHomeomorph M NNReal), (ψ ∈ ht.atlas \ {φ}) ∧ (Overlap φ.source
          ψ.source) := by
          simp only [not_exists, not_and] at contains
          exact find_overlap ht (ChartedSpace.chart_mem_atlas x) (ChartedSpace.mem_chart_source
              x) contains
        let ψ := this.choose
        let ⟨ hψ, overlap ⟩ := this.choose_spec
        have hφ := ht.is_interval φ (ChartedSpace.chart_mem_atlas x)
        by_cases hφIoo : ∃ x y, Set.Ioo x y = φ.target
        · have hψ'' := ht.is_interval ψ (Set.mem_of_mem_sdiff hψ)
          by_cases hψIoo : ∃ x y, Set.Ioo x y = ψ.target
          · -- the O O case
            let a : OChart M := { φ with target_ioo := hφIoo }
            let b : OChart M := { ψ with target_ioo := hψIoo }
            let result := handleOO a b overlap
            rcases result with (result|result)
            · left
              exact result
            · rcases result with ⟨ f, hf ⟩
              let f := f.toIChart
              have ⟨ ht', ht'' ⟩ := replaceCharts ht (ChartedSpace.chart_mem_atlas x)
                  (Set.mem_of_mem_sdiff hψ) overlap f hf
              simp only [Set.mem_ofPred_eq] at ht''
              exact classification' ht'
          · have hψIio : ∃ x, Set.Iio x = ψ.target := Or.elim hψ'' (fun x => False.elim (hψIoo
              x)) id
            -- an O H case
            let a : OChart M := { φ with target_ioo := hφIoo }
            let b : HChart M := { ψ with target_iio := hψIio }
            let result := handleOH a b overlap
            rcases result with ⟨ f, hf ⟩
            let f := f.toIChart
            have ⟨ ht', ht'' ⟩ := replaceCharts ht (ChartedSpace.chart_mem_atlas x)
                (Set.mem_of_mem_sdiff hψ) overlap f hf
            simp only [Set.mem_ofPred_eq] at ht''
            exact classification' ht'
        · have hφIio : ∃ x, Set.Iio x = φ.target := Or.elim hφ (fun x => False.elim (hφIoo x)) id
          have hψ'' := ht.is_interval ψ (Set.mem_of_mem_sdiff hψ)
          by_cases hψIoo : ∃ x y, Set.Ioo x y = ψ.target
          · -- an H O case
            let a : HChart M := { φ with target_iio := hφIio }
            let b : OChart M := { ψ with target_ioo := hψIoo }
            let result := handleOH b a (overlap_symm overlap)
            rcases result with ⟨ f, hf ⟩
            let f := f.toIChart
            have ⟨ ht', ht'' ⟩ := replaceCharts ht (Set.mem_of_mem_sdiff hψ)
                (ChartedSpace.chart_mem_atlas x) (overlap_symm overlap) f hf
            simp only [Set.mem_ofPred_eq] at ht''
            exact classification' ht'
          · have hψIio : ∃ x, Set.Iio x = ψ.target := Or.elim hψ'' (fun x => False.elim (hψIoo
              x)) id
            -- the H H case
            right
            let a : HChart M := { φ with target_iio := hφIio }
            let b : HChart M := { ψ with target_iio := hψIio }
            exact handleHH a b overlap
    · -- A compact manifold must have more than one chart
      exfalso
      apply nonempty'
      push Not at nonempty'
      have : ht.atlas ⊆ {φ} := Set.sdiff_eq_empty.mp nonempty'
      have hone : Nat.card ({φ} : Set _) = 1 := by exact Nat.card_unique
      have : Nat.card (ht.atlas) ≤ Nat.card ({φ} : Set _)  := by
        refine Nat.card_mono ?_ this
        exact Set.finite_singleton φ
      have t' := more_than_one_chart ht
      linarith
termination_by Set.ncard ht.atlas
decreasing_by
  · simp only [Nat.card_coe_set_eq, Set.mem_ofPred_eq] at ht''
    rw [ht'']
    simp only [tsub_lt_self_iff, zero_lt_one, and_true]
    exact (Set.natCard_pos ht.is_finite).mpr (nonempty_atlas ht)
  · simp only [Nat.card_coe_set_eq, Set.mem_ofPred_eq] at ht''
    refine Nat.lt_of_le_pred ?_ ht''
    exact (Set.natCard_pos ht.is_finite).mpr nonempty
  · simp only [Nat.card_coe_set_eq, Set.mem_ofPred_eq] at ht''
    refine Nat.lt_of_le_pred ?_ ht''
    exact (Set.natCard_pos ht.is_finite).mpr nonempty
  · simp only [Nat.card_coe_set_eq, Set.mem_ofPred_eq] at ht''
    refine Nat.lt_of_le_pred ?_ ht''
    exact (Set.natCard_pos ht.is_finite).mpr nonempty

/-- A compact connected Hausdorff manifold charted on the half-line is a circle or an interval. -/
noncomputable def classification [T2Space M] [CompactSpace M] (ht : ChartedSpace NNReal M) :
    (Homeomorph M Circle) ⊕ (Homeomorph M UnitInterval) :=
  let ht' := nicelyCharted ht
  let ht'' := intervalCharted ht'
  classification' (finitelyIntervalCharted ht'')
