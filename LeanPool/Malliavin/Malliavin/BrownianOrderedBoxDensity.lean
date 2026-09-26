/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.BrownianIterated

/-!
# Density of ordered boxes in Brownian simplex kernels

Finite unions of positive ordered time boxes are measure-dense in the strict simplex.  Their
indicators lie in the range of the ordered-box linear map, so simple-function density proves that
this map has dense range at every positive order.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal symmDiff

namespace Malliavin.BrownianIteratedConstruction

private theorem exists_orderedBox_subset_open {n : ℕ}
    (x : Fin n → ℝ≥0) (hx : x ∈ simplex ℝ≥0 n)
    (hpos : ∀ i, 0 < x i) {U : Set (Fin n → ℝ≥0)}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a : OrderedBoxIndex n,
      x ∈ Set.univ.pi (fun i ↦ Set.Ioo (a.u i) (a.v i)) ∧
        orderedBox a.u a.v ⊆ U := by
  cases n with
  | zero =>
      let a : OrderedBoxIndex 0 :=
        { u := fun i ↦ Fin.elim0 i
          v := fun i ↦ Fin.elim0 i
          valid := fun i ↦ Fin.elim0 i
          ordered := fun i ↦ Fin.elim0 i }
      refine ⟨a, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro y _hy
        have hyx : y = x := funext fun i ↦ Fin.elim0 i
        simpa [hyx] using hxU
  | succ k =>
      rcases (isOpen_pi_iff'.mp hU x hxU) with ⟨O, hO, hOU⟩
      have hOnhds : ∀ i, O i ∈ nhds (x i) := fun i ↦ (hO i).1.mem_nhds (hO i).2
      choose l r hlr hlrO using fun i ↦
        (mem_nhds_iff_exists_Ioo_subset' ⟨0, hpos i⟩ (exists_gt (x i))).mp (hOnhds i)
      choose s hxs hsr using fun i ↦ exists_between (hlr i).2
      have hgap : ∀ i : Fin k, x i.castSucc < x i.succ := fun i ↦
        (mem_simplex.mp hx) (Fin.castSucc_lt_succ_iff.mpr le_rfl)
      choose q hxq hqx using fun i ↦ exists_between (hgap i)
      let u : Fin (k + 1) → ℝ≥0 := fun i ↦
        if hi : i = 0 then l i else max (l i) (q (i.pred hi))
      let v : Fin (k + 1) → ℝ≥0 := fun i ↦
        if hi : i = Fin.last k then s i else min (s i) (q (i.castPred hi))
      have hux : ∀ i, u i < x i := by
        intro i
        simp only [u]
        split_ifs with hi
        · exact (hlr i).1
        · rw [max_lt_iff]
          refine ⟨(hlr i).1, ?_⟩
          have hpred : (i.pred hi).succ = i := Fin.succ_pred i hi
          simpa only [hpred] using hqx (i.pred hi)
      have hxv : ∀ i, x i < v i := by
        intro i
        simp only [v]
        split_ifs with hi
        · exact hxs i
        · rw [lt_min_iff]
          refine ⟨hxs i, ?_⟩
          have hcast : (i.castPred hi).castSucc = i := Fin.castSucc_castPred i hi
          simpa only [hcast] using hxq (i.castPred hi)
      have hq_mono : Monotone q := by
        intro i j hij
        rcases hij.eq_or_lt with rfl | hij
        · exact le_rfl
        · exact (hqx i).le.trans <|
            ((mem_simplex.mp hx).monotone (Fin.succ_le_castSucc_iff.mpr hij)).trans
              (hxq j).le
      have hvq (i : Fin (k + 1)) (hi : i ≠ Fin.last k) :
          v i ≤ q (i.castPred hi) := by
        simp [v, hi]
      have hqu (i : Fin (k + 1)) (hi : i ≠ 0) :
          q (i.pred hi) ≤ u i := by
        simp [u, hi]
      have hord : ∀ i j, i < j → v i ≤ u j := by
        intro i j hij
        have hi : i ≠ Fin.last k := Fin.ne_last_of_lt hij
        have hj : j ≠ 0 := Fin.ne_zero_of_lt hij
        have hp : i.castPred hi ≤ j.pred hj := by
          exact (Fin.castPred_le_pred_iff hi hj).mpr hij
        exact (hvq i hi).trans ((hq_mono hp).trans (hqu j hj))
      let a : OrderedBoxIndex (k + 1) :=
        { u := u
          v := v
          valid := fun i ↦ (hux i).le.trans (hxv i).le
          ordered := hord }
      refine ⟨a, ?_, ?_⟩
      · intro i _hi
        exact ⟨hux i, hxv i⟩
      · intro y hy
        apply hOU
        intro i _hi
        apply hlrO i
        have hyi : y i ∈ Set.Ioc (u i) (v i) := hy i (Set.mem_univ i)
        have hlu : l i ≤ u i := by
          simp only [u]
          split_ifs
          · exact le_rfl
          · exact le_max_left _ _
        have hvs : v i ≤ s i := by
          simp only [v]
          split_ifs
          · exact le_rfl
          · exact min_le_left _ _
        exact ⟨hlu.trans_lt hyi.1, (hyi.2.trans hvs).trans_lt (hsr i)⟩

private def emptyOrderedBoxIndex (n : ℕ) : OrderedBoxIndex (n + 1) where
  u := 0
  v := 0
  valid := fun _ ↦ le_rfl
  ordered := fun _ _ _ ↦ le_rfl

private theorem orderedBox_emptyOrderedBoxIndex (n : ℕ) :
    orderedBox (emptyOrderedBoxIndex n).u (emptyOrderedBoxIndex n).v = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨y, hy⟩
  have hzero := hy (0 : Fin (n + 1)) (Set.mem_univ _)
  change 0 < y 0 ∧ y 0 ≤ 0 at hzero
  exact (not_lt_of_ge hzero.2) hzero.1

private theorem exists_orderedBox_biInter {n : ℕ}
    (s : Finset (OrderedBoxIndex (n + 1))) (hs : s.Nonempty) :
    ∃ a : OrderedBoxIndex (n + 1),
      (⋂ b ∈ s, orderedBox b.u b.v) = orderedBox a.u a.v := by
  classical
  by_cases hne : (⋂ b ∈ s, orderedBox b.u b.v).Nonempty
  · let u : Fin (n + 1) → ℝ≥0 := fun i ↦ s.sup' hs fun b ↦ b.u i
    let v : Fin (n + 1) → ℝ≥0 := fun i ↦ s.inf' hs fun b ↦ b.v i
    obtain ⟨z, hz⟩ := hne
    have hzb (b : OrderedBoxIndex (n + 1)) (hb : b ∈ s) :
        z ∈ orderedBox b.u b.v := by
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hz b) hb
    have hvalid : ∀ i, u i ≤ v i := by
      intro i
      have huz : u i < z i := by
        simp only [u]
        rw [Finset.sup'_lt_iff]
        intro b hb
        exact (hzb b hb i (Set.mem_univ i)).1
      have hzv : z i ≤ v i := by
        apply Finset.le_inf' hs
        intro b hb
        exact (hzb b hb i (Set.mem_univ i)).2
      exact huz.le.trans hzv
    have hordered : ∀ i j, i < j → v i ≤ u j := by
      intro i j hij
      obtain ⟨b, hb⟩ := hs
      exact (Finset.inf'_le (f := fun a ↦ a.v i) hb).trans <|
        (b.ordered i j hij).trans (Finset.le_sup' (f := fun a ↦ a.u j) hb)
    let a : OrderedBoxIndex (n + 1) :=
      { u := u
        v := v
        valid := hvalid
        ordered := hordered }
    refine ⟨a, Set.Subset.antisymm ?_ ?_⟩
    · intro y hy i _hi
      have hui : u i < y i := by
        simp only [u]
        rw [Finset.sup'_lt_iff]
        intro b hb
        exact (Set.mem_iInter.mp (Set.mem_iInter.mp hy b) hb
          i (Set.mem_univ i)).1
      have hvi : y i ≤ v i := by
        apply Finset.le_inf' hs
        intro b hb
        exact (Set.mem_iInter.mp (Set.mem_iInter.mp hy b) hb
          i (Set.mem_univ i)).2
      exact ⟨hui, hvi⟩
    · intro y hy
      rw [Set.mem_iInter₂]
      intro b hb i _hi
      have hyi := hy i (Set.mem_univ i)
      exact ⟨(Finset.le_sup' (f := fun a ↦ a.u i) hb).trans_lt hyi.1,
        hyi.2.trans (Finset.inf'_le (f := fun a ↦ a.v i) hb)⟩
  · refine ⟨emptyOrderedBoxIndex n, ?_⟩
    rw [orderedBox_emptyOrderedBoxIndex]
    exact Set.not_nonempty_iff_eq_empty.mp hne

private noncomputable def orderedBoxInterIndex {n : ℕ}
    (a b : OrderedBoxIndex (n + 1)) : OrderedBoxIndex (n + 1) := by
  classical
  exact Classical.choose (exists_orderedBox_biInter ({a, b} : Finset _) (by simp))

private theorem orderedBox_inter_eq {n : ℕ} (a b : OrderedBoxIndex (n + 1)) :
    orderedBox a.u a.v ∩ orderedBox b.u b.v =
      orderedBox (orderedBoxInterIndex a b).u (orderedBoxInterIndex a b).v := by
  classical
  have h := Classical.choose_spec
    (exists_orderedBox_biInter ({a, b} : Finset _) (by simp))
  simpa [orderedBoxInterIndex, Set.inter_comm] using h

private theorem indicatorConstLp_union_eq_add_sub_inter
    {X : Type*} [MeasurableSpace X] (m : Measure X) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hms : m s ≠ ∞) (hmt : m t ≠ ∞) :
    indicatorConstLp 2 (hs.union ht) (by finiteness) (1 : ℝ) =
      indicatorConstLp 2 hs hms (1 : ℝ) + indicatorConstLp 2 ht hmt (1 : ℝ) -
        indicatorConstLp 2 (hs.inter ht) (by finiteness) (1 : ℝ) := by
  ext1
  grw [Lp.coeFn_sub, Lp.coeFn_add, indicatorConstLp_coeFn,
    indicatorConstLp_coeFn, indicatorConstLp_coeFn, indicatorConstLp_coeFn]
  filter_upwards [] with x
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt]

private def finiteOrderedBoxUnions (n : ℕ) : Set (Set (Fin (n + 1) → ℝ≥0)) :=
  {t | ∃ s : Finset (OrderedBoxIndex (n + 1)),
    t = ⋃ a ∈ s, orderedBox a.u a.v}

private theorem restrictedSimplexMeasure_finiteOrderedBoxUnion_ne_top
    {n : ℕ} {I : Type*} (s : Finset I) (a : I → OrderedBoxIndex (n + 1)) :
    ((iteratedKernelMeasure (n + 1)).restrict (simplex ℝ≥0 (n + 1)))
      (⋃ i ∈ s, orderedBox (a i).u (a i).v) ≠ ∞ := by
  apply measure_biUnion_ne_top s.finite_toSet
  intro i _hi
  exact restrictedSimplexMeasure_orderedBox_ne_top (a i)

private noncomputable def finiteOrderedBoxUnionKernel
    {n : ℕ} {I : Type*} (s : Finset I) (a : I → OrderedBoxIndex (n + 1)) :
    IteratedIntegralConstruction.SimplexKernel (n + 1) :=
  indicatorConstLp 2
    (Finset.measurableSet_biUnion s fun i _hi ↦ measurableSet_orderedBox (a i).u (a i).v)
    (restrictedSimplexMeasure_finiteOrderedBoxUnion_ne_top s a) (1 : ℝ)

private theorem finiteOrderedBoxUnionKernel_insert
    {n : ℕ} {I : Type*} [DecidableEq I] (s : Finset I) (i : I)
    (a : I → OrderedBoxIndex (n + 1)) :
    finiteOrderedBoxUnionKernel (insert i s) a =
      orderedBoxSimplexKernel (a i) + finiteOrderedBoxUnionKernel s a -
        finiteOrderedBoxUnionKernel s (fun j ↦ orderedBoxInterIndex (a i) (a j)) := by
  let μ := (iteratedKernelMeasure (n + 1)).restrict (simplex ℝ≥0 (n + 1))
  let B := orderedBox (a i).u (a i).v
  let T := ⋃ j ∈ s, orderedBox (a j).u (a j).v
  have hB : MeasurableSet B := measurableSet_orderedBox _ _
  have hT : MeasurableSet T :=
    Finset.measurableSet_biUnion s fun j _hj ↦ measurableSet_orderedBox _ _
  have hμB : μ B ≠ ∞ := restrictedSimplexMeasure_orderedBox_ne_top (a i)
  have hμT : μ T ≠ ∞ := restrictedSimplexMeasure_finiteOrderedBoxUnion_ne_top s a
  have hinter : B ∩ T =
      ⋃ j ∈ s, orderedBox (orderedBoxInterIndex (a i) (a j)).u
        (orderedBoxInterIndex (a i) (a j)).v := by
    ext x
    constructor
    · rintro ⟨hxB, hxT⟩
      rcases Set.mem_iUnion.mp hxT with ⟨j, hxj⟩
      rcases Set.mem_iUnion.mp hxj with ⟨hjs, hxj⟩
      apply Set.mem_iUnion_of_mem j
      apply Set.mem_iUnion_of_mem hjs
      rw [← orderedBox_inter_eq]
      exact ⟨hxB, hxj⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
      rcases Set.mem_iUnion.mp hxj with ⟨hjs, hxj⟩
      rw [← orderedBox_inter_eq] at hxj
      exact ⟨hxj.1, Set.mem_iUnion_of_mem j (Set.mem_iUnion_of_mem hjs hxj.2)⟩
  have hformula := indicatorConstLp_union_eq_add_sub_inter μ hB hT hμB hμT
  simpa only [finiteOrderedBoxUnionKernel, orderedBoxSimplexKernel, B, T,
    Finset.set_biUnion_insert, hinter] using hformula

private theorem finiteOrderedBoxUnionKernel_mem_range
    {n : ℕ} {I : Type*} (s : Finset I) (a : I → OrderedBoxIndex (n + 1)) :
    finiteOrderedBoxUnionKernel s a ∈ LinearMap.range (orderedBoxToSimplexKernel (n + 1)) := by
  classical
  induction s using Finset.induction generalizing a with
  | empty =>
      simp [finiteOrderedBoxUnionKernel]
  | @insert i s hi ih =>
      rw [finiteOrderedBoxUnionKernel_insert s i a]
      apply Submodule.sub_mem
      · apply Submodule.add_mem
        · refine ⟨Finsupp.single (a i) 1, ?_⟩
          simp only [orderedBoxToSimplexKernel_single, one_smul]
        · exact ih a
      · exact ih (fun j ↦ orderedBoxInterIndex (a i) (a j))

private theorem indicatorConstLp_eq_smul_one
    {X : Type*} [MeasurableSpace X] (m : Measure X) {s : Set X}
    (hs : MeasurableSet s) (hms : m s ≠ ∞) (c : ℝ) :
    indicatorConstLp 2 hs hms c = c • indicatorConstLp 2 hs hms (1 : ℝ) := by
  ext1
  grw [Lp.coeFn_smul, indicatorConstLp_coeFn, indicatorConstLp_coeFn]
  filter_upwards [] with x
  by_cases hx : x ∈ s <;> simp [hx]

private theorem restrictedSimplexMeasure_boundary_zero (n : ℕ) :
    ((iteratedKernelMeasure (n + 1)).restrict (simplex ℝ≥0 (n + 1)))
      {x | x 0 = 0} = 0 := by
  apply le_antisymm
  · refine (Measure.restrict_apply_le _ _).trans ?_
    change iteratedKernelMeasure (n + 1) {x | x 0 = 0} ≤ 0
    rw [iteratedKernelMeasure, Measure.pi_hyperplane]
  · exact bot_le

private theorem measureDense_finiteOrderedBoxUnions (n : ℕ) :
    ((iteratedKernelMeasure (n + 1)).restrict (simplex ℝ≥0 (n + 1))).MeasureDense
      (finiteOrderedBoxUnions n) := by
  classical
  let μ := (iteratedKernelMeasure (n + 1)).restrict (simplex ℝ≥0 (n + 1))
  let S := simplex ℝ≥0 (n + 1)
  let Z : Set (Fin (n + 1) → ℝ≥0) := {x | x 0 = 0}
  have hS : MeasurableSet S := measurableSet_simplex (n + 1)
  have hZ : MeasurableSet Z := by
    exact measurableSet_singleton 0 |>.preimage (measurable_pi_apply 0)
  have hμZ : μ Z = 0 := restrictedSimplexMeasure_boundary_zero n
  constructor
  · rintro t ⟨s, rfl⟩
    exact Finset.measurableSet_biUnion s fun a _ha ↦ measurableSet_orderedBox a.u a.v
  · intro s hs hμs ε hε
    let A := s ∩ S
    have hA : MeasurableSet A := hs.inter hS
    have hμA : μ A ≠ ∞ := ne_top_of_le_ne_top hμs (measure_mono Set.inter_subset_left)
    have heps : ENNReal.ofReal ε ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hε
    have hhalf : ENNReal.ofReal ε / 2 ≠ 0 := (ENNReal.half_pos heps).ne'
    rcases hA.exists_isOpen_symmDiff_lt hμA hhalf with ⟨U, hU, _hμU, hUA⟩
    let C := (A ∩ U) \ Z
    have hC : MeasurableSet C := (hA.inter hU.measurableSet).diff hZ
    have hμC : μ C ≠ ∞ :=
      ne_top_of_le_ne_top hμA (measure_mono <| Set.sdiff_subset.trans Set.inter_subset_left)
    rcases hC.exists_isCompact_sdiff_lt hμC hhalf with ⟨K, hKC, hK, hCK⟩
    have hKsimplex : K ⊆ S := by
      exact hKC.trans <|
        Set.sdiff_subset.trans (Set.inter_subset_left.trans Set.inter_subset_right)
    have hKopen : K ⊆ U := by
      exact hKC.trans <| Set.sdiff_subset.trans Set.inter_subset_right
    have hKnotZ : ∀ x ∈ K, x ∉ Z := by
      intro x hxK
      exact (hKC hxK).2
    have hlocal : ∀ x : K, ∃ a : OrderedBoxIndex (n + 1),
        x.1 ∈ Set.univ.pi (fun i ↦ Set.Ioo (a.u i) (a.v i)) ∧
          orderedBox a.u a.v ⊆ U := by
      intro x
      have hx0 : 0 < x.1 0 := pos_iff_ne_zero.mpr fun hxzero ↦
        hKnotZ x.1 x.2 hxzero
      have hxpos : ∀ i, 0 < x.1 i := fun i ↦
        hx0.trans_le ((mem_simplex.mp (hKsimplex x.2)).monotone (Fin.zero_le i))
      exact exists_orderedBox_subset_open x.1 (hKsimplex x.2) hxpos hU (hKopen x.2)
    choose a hxa haU using hlocal
    let V : K → Set (Fin (n + 1) → ℝ≥0) := fun x ↦
      Set.univ.pi (fun i ↦ Set.Ioo ((a x).u i) ((a x).v i))
    have hVopen : ∀ x, IsOpen (V x) := fun x ↦
      isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo
    have hKV : K ⊆ ⋃ x, V x := by
      intro x hxK
      exact Set.mem_iUnion.mpr ⟨⟨x, hxK⟩, hxa ⟨x, hxK⟩⟩
    rcases hK.elim_finite_subcover V hVopen hKV with ⟨T, hKT⟩
    let t := ⋃ x ∈ T, orderedBox (a x).u (a x).v
    have htmem : t ∈ finiteOrderedBoxUnions n := by
      refine ⟨T.image a, ?_⟩
      ext x
      simp [t]
    have hKt : K ⊆ t := by
      intro x hxK
      rcases Set.mem_iUnion.mp (hKT hxK) with ⟨y, hy⟩
      rcases Set.mem_iUnion.mp hy with ⟨hyT, hxy⟩
      apply Set.mem_iUnion_of_mem y
      apply Set.mem_iUnion_of_mem hyT
      intro i _hi
      have hi := hxy i (Set.mem_univ i)
      exact ⟨hi.1, hi.2.le⟩
    have htU : t ⊆ U := by
      intro x hxt
      rcases Set.mem_iUnion.mp hxt with ⟨y, hy⟩
      rcases Set.mem_iUnion.mp hy with ⟨hyT, hxy⟩
      exact haU y hxy
    have htS : t ⊆ S := by
      intro x hxt
      rcases Set.mem_iUnion.mp hxt with ⟨y, hy⟩
      rcases Set.mem_iUnion.mp hy with ⟨hyT, hxy⟩
      exact orderedBox_subset_simplex (a y) hxy
    have hsymm : A ∆ t ⊆ (U ∆ A) ∪ ((C \ K) ∪ Z) := by
      intro x hx
      rw [symmDiff_def] at hx ⊢
      rcases hx with hx | hx
      · by_cases hxU : x ∈ U
        · by_cases hxZ : x ∈ Z
          · exact Or.inr (Or.inr hxZ)
          · exact Or.inr <| Or.inl
              ⟨⟨⟨hx.1, hxU⟩, hxZ⟩, fun hxK ↦ hx.2 (hKt hxK)⟩
        · exact Or.inl <| Or.inr ⟨hx.1, hxU⟩
      · exact Or.inl <| Or.inl ⟨htU hx.1, hx.2⟩
    have hAt : μ (A ∆ t) < ENNReal.ofReal ε := by
      calc
        μ (A ∆ t) ≤ μ ((U ∆ A) ∪ ((C \ K) ∪ Z)) := measure_mono hsymm
        _ ≤ μ (U ∆ A) + (μ (C \ K) + μ Z) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
        _ < ENNReal.ofReal ε / 2 + ENNReal.ofReal ε / 2 := by
          apply ENNReal.add_lt_add hUA
          simpa only [hμZ, add_zero] using hCK
        _ = ENNReal.ofReal ε := ENNReal.add_halves _
    refine ⟨t, htmem, ?_⟩
    have hst : MeasurableSet (s ∆ t) := hs.symmDiff <|
      Finset.measurableSet_biUnion T fun x _hx ↦ measurableSet_orderedBox (a x).u (a x).v
    have hAtm : MeasurableSet (A ∆ t) := hA.symmDiff <|
      Finset.measurableSet_biUnion T fun x _hx ↦ measurableSet_orderedBox (a x).u (a x).v
    change ((iteratedKernelMeasure (n + 1)).restrict (simplex ℝ≥0 (n + 1)))
      (s ∆ t) < ENNReal.ofReal ε
    change ((iteratedKernelMeasure (n + 1)).restrict (simplex ℝ≥0 (n + 1)))
      (A ∆ t) < ENNReal.ofReal ε at hAt
    rw [Measure.restrict_apply hst]
    rw [Measure.restrict_apply hAtm] at hAt
    have hset : (s ∆ t) ∩ simplex ℝ≥0 (n + 1) =
        (A ∆ t) ∩ simplex ℝ≥0 (n + 1) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_symmDiff]
      constructor
      · rintro ⟨hst, hxS⟩
        rcases hst with ⟨hxs, hxt⟩ | ⟨hxt, hxs⟩
        · exact ⟨Or.inl ⟨⟨hxs, hxS⟩, hxt⟩, hxS⟩
        · exact ⟨Or.inr ⟨hxt, fun hxA ↦ hxs hxA.1⟩, hxS⟩
      · rintro ⟨hAt', hxS⟩
        rcases hAt' with ⟨⟨hxs, _⟩, hxt⟩ | ⟨hxt, hxs⟩
        · exact ⟨Or.inl ⟨hxs, hxt⟩, hxS⟩
        · exact ⟨Or.inr ⟨hxt, fun hxs' ↦ hxs ⟨hxs', hxS⟩⟩, hxS⟩
    rwa [hset]

/-- Indicators of ordered time boxes have dense span in every positive-order simplex kernel
space. -/
theorem orderedBoxDense_succ (n : ℕ) : OrderedBoxDense (n + 1) := by
  let _ : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let μ := (iteratedKernelMeasure (n + 1)).restrict (simplex ℝ≥0 (n + 1))
  let L := orderedBoxToSimplexKernel (n + 1)
  let R := LinearMap.range L
  have hMD := measureDense_finiteOrderedBoxUnions n
  have hone {s : Set (Fin (n + 1) → ℝ≥0)} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
      indicatorConstLp 2 hs hμs (1 : ℝ) ∈ R.topologicalClosure := by
    have happrox := hMD.indicatorConstLp_subset_closure 2 (1 : ℝ)
      ⟨s, hs, hμs, rfl⟩
    apply (closure_minimal _ R.isClosed_topologicalClosure) happrox
    rintro f ⟨t, ht, hμt, rfl⟩
    rcases ht with ⟨u, rfl⟩
    apply R.le_topologicalClosure
    change finiteOrderedBoxUnionKernel u id ∈ R
    exact finiteOrderedBoxUnionKernel_mem_range u id
  have hall : ∀ f : IteratedIntegralConstruction.SimplexKernel (n + 1),
      f ∈ R.topologicalClosure := by
    refine Lp.induction (by norm_num) (motive := fun f ↦ f ∈ R.topologicalClosure)
      ?_ ?_ R.isClosed_topologicalClosure
    · intro c s hs hμs
      change indicatorConstLp 2 hs hμs.ne c ∈ R.topologicalClosure
      rw [indicatorConstLp_eq_smul_one μ hs hμs.ne c]
      exact R.topologicalClosure.smul_mem c (hone hs hμs.ne)
    · intro f g hf hg _hdisjoint hfm hgm
      exact R.topologicalClosure.add_mem hfm hgm
  have htop : R.topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    intro f _hf
    exact hall f
  change Dense (Set.range (orderedBoxToSimplexKernel (n + 1)))
  rw [← LinearMap.coe_range]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr htop

/-- Ordered-box density at every positive order. -/
theorem positiveOrderedBoxDense : PositiveOrderedBoxDense :=
  orderedBoxDense_succ

/-- The canonical completed Brownian iterated-integral family, with ordered-box density
discharged. -/
noncomputable def brownianIteratedIntegralFamily
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    IteratedIntegralFamily P :=
  family hB hsm positiveOrderedBoxDense

/-- The canonical completed family agrees with Brownian increment products on every ordered
box. -/
theorem brownianIteratedIntegralFamily_isBrownian
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    (brownianIteratedIntegralFamily hB hsm).IsBrownian B :=
  family_isBrownian hB hsm positiveOrderedBoxDense

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
