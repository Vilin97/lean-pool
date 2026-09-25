/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector

/-! # Simplex-sector conversion: arbitrary order

The general case of the simplex-sector conversion.  Develops the standard
ordered simplices in `Fin n → ℝ` (measurability, compactness, head/tail
decomposition), transports set integrals over ordered cube sectors through
the ordered coordinate equivalences, proves that for continuous integrands
the recursive nested simplex integral equals the set integral over the
closed finite ordered simplex, and concludes that under the global
smoothness hypothesis every recursive ordered contribution equals the
corresponding closed ordered cube-sector contribution.
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/--
Generic measurability of an ordered-simplex predicate evaluated on a finite
list of measurable real-valued coordinate functions.
-/
theorem measurableSet_orderedSimplexParams_map
    {α : Type*} [MeasurableSpace α] :
    ∀ (fs : List (α → ℝ)) {topFn : α → ℝ},
      Measurable topFn →
      (∀ f ∈ fs, Measurable f) →
      MeasurableSet
        {x : α | OrderedSimplexParams (topFn x) (fs.map fun f => f x)}
  | [], _topFn, _htop, _hfs => by
      simp
  | f :: fs, topFn, htop, hfs => by
      have hf : Measurable f := hfs f (by simp)
      have htail :
          ∀ g ∈ fs, Measurable g := by
        intro g hg
        exact hfs g (List.mem_cons_of_mem f hg)
      simp only [List.map_cons, orderedSimplexParams_cons, Set.ofPred_and]
      simpa [Set.inter_assoc] using
        (((measurableSet_le
              (measurable_const : Measurable fun _ : α => (0 : ℝ))
              hf).inter
            (measurableSet_le hf htop)).inter
          (measurableSet_orderedSimplexParams_map fs hf htail))

omit [Fintype V] [DecidableEq V] in
/--
Closedness of an ordered-simplex predicate evaluated on a finite list of
continuous real-valued coordinate functions.
-/
theorem isClosed_orderedSimplexParams_map
    {α : Type*} [TopologicalSpace α] :
    ∀ (fs : List (α → ℝ)) {topFn : α → ℝ},
      Continuous topFn →
      (∀ f ∈ fs, Continuous f) →
      IsClosed
        {x : α | OrderedSimplexParams (topFn x) (fs.map fun f => f x)}
  | [], _topFn, _htop, _hfs => by
      simp
  | f :: fs, topFn, htop, hfs => by
      have hf : Continuous f := hfs f (by simp)
      have htail :
          ∀ g ∈ fs, Continuous g := by
        intro g hg
        exact hfs g (List.mem_cons_of_mem f hg)
      simp only [List.map_cons, orderedSimplexParams_cons, Set.ofPred_and]
      simpa [Set.inter_assoc] using
        (((isClosed_le
              (continuous_const : Continuous fun _ : α => (0 : ℝ))
              hf).inter
            (isClosed_le hf htop)).inter
          (isClosed_orderedSimplexParams_map fs hf htail))

omit [Fintype V] [DecidableEq V] in
/-- The ordered-simplex predicate on `Fin n` coordinate tuples is measurable. -/
theorem measurableSet_orderedSimplexParams_ofFn (n : ℕ) :
    MeasurableSet
      {ts : Fin n → ℝ | OrderedSimplexParams 1 (List.ofFn ts)} := by
  let fs : List ((Fin n → ℝ) → ℝ) :=
    List.ofFn fun i : Fin n => fun ts : Fin n → ℝ => ts i
  have hfs : ∀ f ∈ fs, Measurable f := by
    simp [fs, measurable_pi_apply]
  have hmeas :
      MeasurableSet
        {ts : Fin n → ℝ |
          OrderedSimplexParams ((fun _ : Fin n → ℝ => (1 : ℝ)) ts)
            (fs.map fun f => f ts)} :=
    measurableSet_orderedSimplexParams_map fs measurable_const hfs
  convert hmeas using 1
  ext ts
  simp [fs, List.map_ofFn, Function.comp_def]

/--
The finite ordered simplex with a variable upper bound. This is the induction
invariant for the ordered-simplex/Fubini bridge.
-/
def orderedFinSimplexWithTop (top : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {ts | OrderedSimplexParams top (List.ofFn ts)}

omit [Fintype V] [DecidableEq V] in
/-- Variable-top finite ordered simplexes are measurable. -/
theorem measurableSet_orderedFinSimplexWithTop (top : ℝ) (n : ℕ) :
    MeasurableSet (orderedFinSimplexWithTop top n) := by
  let fs : List ((Fin n → ℝ) → ℝ) :=
    List.ofFn fun i : Fin n => fun ts : Fin n → ℝ => ts i
  have hfs : ∀ f ∈ fs, Measurable f := by
    simp [fs, measurable_pi_apply]
  have hmeas :
      MeasurableSet
        {ts : Fin n → ℝ |
          OrderedSimplexParams ((fun _ : Fin n → ℝ => top) ts)
            (fs.map fun f => f ts)} :=
    measurableSet_orderedSimplexParams_map fs measurable_const hfs
  convert hmeas using 1
  ext ts
  simp [orderedFinSimplexWithTop, fs, List.map_ofFn, Function.comp_def]

omit [Fintype V] [DecidableEq V] in
/-- Variable-top finite ordered simplexes are closed. -/
theorem isClosed_orderedFinSimplexWithTop (top : ℝ) (n : ℕ) :
    IsClosed (orderedFinSimplexWithTop top n) := by
  let fs : List ((Fin n → ℝ) → ℝ) :=
    List.ofFn fun i : Fin n => fun ts : Fin n → ℝ => ts i
  have hfs : ∀ f ∈ fs, Continuous f := by
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, fs]
    intro i
    exact continuous_apply i
  have hclosed :
      IsClosed
        {ts : Fin n → ℝ |
          OrderedSimplexParams ((fun _ : Fin n → ℝ => top) ts)
            (fs.map fun f => f ts)} :=
    isClosed_orderedSimplexParams_map fs continuous_const hfs
  convert hclosed using 1
  ext ts
  simp [orderedFinSimplexWithTop, fs, List.map_ofFn, Function.comp_def]

omit [Fintype V] [DecidableEq V] in
/-- A variable-top finite ordered simplex is contained in the coordinate box `[0, top]^n`. -/
theorem orderedFinSimplexWithTop_subset_pi_Icc (top : ℝ) (n : ℕ) :
    orderedFinSimplexWithTop top n ⊆
      Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) top := by
  intro ts hts
  rw [Set.mem_univ_pi]
  intro i
  have hparams : OrderedSimplexParams top (List.ofFn ts) := by
    simpa [orderedFinSimplexWithTop] using hts
  have hmem : ts i ∈ List.ofFn ts := by
    simp
  exact ⟨OrderedSimplexParams.nonneg_of_mem hparams hmem,
    OrderedSimplexParams.le_top_of_mem hparams hmem⟩

omit [Fintype V] [DecidableEq V] in
/-- Variable-top finite ordered simplexes are compact. -/
theorem isCompact_orderedFinSimplexWithTop (top : ℝ) (n : ℕ) :
    IsCompact (orderedFinSimplexWithTop top n) := by
  have hbox :
      IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) top) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact IsCompact.of_isClosed_subset hbox
    (isClosed_orderedFinSimplexWithTop top n)
    (orderedFinSimplexWithTop_subset_pi_Icc top n)

omit [Fintype V] [DecidableEq V] in
/-- Continuous functions are integrable on variable-top finite ordered simplexes. -/
theorem integrableOn_orderedFinSimplexWithTop_of_continuous
    {top : ℝ} {n : ℕ} {G : (Fin n → ℝ) → ℝ}
    (hG : Continuous G) :
    IntegrableOn G (orderedFinSimplexWithTop top n) :=
  hG.continuousOn.integrableOn_compact (isCompact_orderedFinSimplexWithTop top n)

omit [Fintype V] [DecidableEq V] in
/-- The original finite sector is the variable-top simplex with top `1`. -/
theorem orderedFinSimplex_eq_orderedFinSimplexWithTop_one (n : ℕ) :
    orderedFinSimplex n = orderedFinSimplexWithTop 1 n := by
  ext ts
  rw [mem_orderedFinSimplex_iff, orderedFinSimplexWithTop]
  constructor
  · intro h
    exact h.2
  · intro h
    constructor
    · intro i
      have hmem : ts i ∈ List.ofFn ts := by
        simp
      exact ⟨OrderedSimplexParams.nonneg_of_mem h hmem,
        OrderedSimplexParams.le_top_of_mem h hmem⟩
    · exact h

omit [Fintype V] [DecidableEq V] in
/-- Head-tail membership characterization for the variable-top finite simplex. -/
theorem mem_orderedFinSimplexWithTop_succ_iff
    (top : ℝ) {n : ℕ} (ts : Fin (n + 1) → ℝ) :
    ts ∈ orderedFinSimplexWithTop top (n + 1) ↔
      0 ≤ ts 0 ∧ ts 0 ≤ top ∧
        Fin.tail ts ∈ orderedFinSimplexWithTop (ts 0) n := by
  change OrderedSimplexParams top (List.ofFn ts) ↔
      0 ≤ ts 0 ∧ ts 0 ≤ top ∧
        Fin.tail ts ∈ orderedFinSimplexWithTop (ts 0) n
  rw [List.ofFn_succ, orderedSimplexParams_cons]
  simp [orderedFinSimplexWithTop, Fin.tail_def]

/--
The head-tail form of the variable-top ordered simplex in product
coordinates.  The first coordinate is the outer simplex variable and the
second coordinate is the tail tuple.
-/
def orderedFinSimplexHeadTail (top : ℝ) (n : ℕ) :
    Set (ℝ × (Fin n → ℝ)) :=
  {z | z.1 ∈ Set.Icc (0 : ℝ) top ∧
    z.2 ∈ orderedFinSimplexWithTop z.1 n}

omit [Fintype V] [DecidableEq V] in
/-- The head-tail ordered simplex sector is measurable. -/
theorem measurableSet_orderedFinSimplexHeadTail (top : ℝ) (n : ℕ) :
    MeasurableSet (orderedFinSimplexHeadTail top n) := by
  have hhead : MeasurableSet {z : ℝ × (Fin n → ℝ) | z.1 ∈ Set.Icc (0 : ℝ) top} :=
    measurableSet_Icc.preimage measurable_fst
  let fs : List ((ℝ × (Fin n → ℝ)) → ℝ) :=
    List.ofFn fun i : Fin n => fun z : ℝ × (Fin n → ℝ) => z.2 i
  have hfs : ∀ f ∈ fs, Measurable f := by
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, fs]
    intro i
    exact (measurable_pi_apply i).comp measurable_snd
  have htail :
      MeasurableSet
        {z : ℝ × (Fin n → ℝ) |
          OrderedSimplexParams z.1 (List.ofFn z.2)} := by
    have hmeas :
        MeasurableSet
          {z : ℝ × (Fin n → ℝ) |
            OrderedSimplexParams ((fun z : ℝ × (Fin n → ℝ) => z.1) z)
              (fs.map fun f => f z)} :=
      measurableSet_orderedSimplexParams_map fs measurable_fst hfs
    convert hmeas using 1
    ext z
    simp [fs, List.map_ofFn, Function.comp_def]
  rw [orderedFinSimplexHeadTail]
  exact hhead.inter htail

omit [Fintype V] [DecidableEq V] in
/--
The `piFinSuccAbove` coordinate split identifies the `(n+1)`-dimensional
ordered simplex with its head-tail product-coordinate sector.
-/
theorem orderedFinSimplexWithTop_succ_eq_piFinSuccAbove_preimage_headTail
    (top : ℝ) (n : ℕ) :
    orderedFinSimplexWithTop top (n + 1) =
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0) ⁻¹'
        orderedFinSimplexHeadTail top n := by
  let φ : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  ext ts
  rw [mem_orderedFinSimplexWithTop_succ_iff]
  change
    (0 ≤ ts 0 ∧ ts 0 ≤ top ∧
        Fin.tail ts ∈ orderedFinSimplexWithTop (ts 0) n) ↔
      φ ts ∈ orderedFinSimplexHeadTail top n
  simp only [Fin.tail_def, orderedFinSimplexHeadTail, Set.mem_Icc,
    MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.zero_succAbove,
    Fin.insertNth_zero', Fin.removeNth_zero, Equiv.symm_mk, Equiv.coe_fn_mk, Set.mem_ofPred_eq, φ]
  constructor
  · rintro ⟨h0, htop, htail⟩
    exact ⟨⟨h0, htop⟩, htail⟩
  · rintro ⟨⟨h0, htop⟩, htail⟩
    exact ⟨h0, htop, htail⟩

omit [Fintype V] [DecidableEq V] in
/--
Measure transport from the `(n+1)`-coordinate finite simplex to its explicit
head-tail sector.
-/
theorem setIntegral_orderedFinSimplexWithTop_succ_eq_headTail
    (top : ℝ) (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts =
      ∫ z in orderedFinSimplexHeadTail top n,
        f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => ℝ) 0).symm z) := by
  let φ : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hsector :
      orderedFinSimplexWithTop top (n + 1) =
        φ ⁻¹' orderedFinSimplexHeadTail top n := by
    exact orderedFinSimplexWithTop_succ_eq_piFinSuccAbove_preimage_headTail top n
  rw [hsector]
  have hpre :=
    (MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding φ)
      (fun z : ℝ × (Fin n → ℝ) => f (φ.symm z))
      (orderedFinSimplexHeadTail top n)
  have hmeas : MeasurableSet (φ ⁻¹' orderedFinSimplexHeadTail top n) := by
    rw [← hsector]
    exact measurableSet_orderedFinSimplexWithTop top (n + 1)
  have hcongr :
      ∫ ts in φ ⁻¹' orderedFinSimplexHeadTail top n, f ts =
        ∫ ts in φ ⁻¹' orderedFinSimplexHeadTail top n, f (φ.symm (φ ts)) := by
    apply setIntegral_congr_fun hmeas
    intro ts _hts
    exact congrArg f (φ.left_inv ts).symm
  exact hcongr.trans hpre

omit [Fintype V] [DecidableEq V] in
/--
Fubini split for the head-tail finite ordered simplex sector.
-/
theorem setIntegral_orderedFinSimplexHeadTail_eq_iterated_Icc
    (top : ℝ) (n : ℕ) (f : ℝ × (Fin n → ℝ) → ℝ)
    (hf : IntegrableOn f (orderedFinSimplexHeadTail top n)) :
    ∫ z in orderedFinSimplexHeadTail top n, f z =
      ∫ t in Set.Icc (0 : ℝ) top,
        ∫ us in orderedFinSimplexWithTop t n, f (t, us) := by
  let rect : Set (ℝ × (Fin n → ℝ)) :=
    Set.Icc (0 : ℝ) top ×ˢ (Set.univ : Set (Fin n → ℝ))
  have hrect_inter : rect ∩ orderedFinSimplexHeadTail top n =
      orderedFinSimplexHeadTail top n := by
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      exact ⟨⟨hz.1, trivial⟩, hz⟩
  have hsector : MeasurableSet (orderedFinSimplexHeadTail top n) :=
    measurableSet_orderedFinSimplexHeadTail top n
  have hind :
      IntegrableOn ((orderedFinSimplexHeadTail top n).indicator f) rect
        (volume : Measure (ℝ × (Fin n → ℝ))) :=
    (hf.integrable_indicator hsector).integrableOn
  calc
    ∫ z in orderedFinSimplexHeadTail top n, f z
        = ∫ z in rect, (orderedFinSimplexHeadTail top n).indicator f z := by
          rw [setIntegral_indicator hsector]
          rw [hrect_inter]
    _ = ∫ t in Set.Icc (0 : ℝ) top,
          ∫ us in (Set.univ : Set (Fin n → ℝ)),
            (orderedFinSimplexHeadTail top n).indicator f (t, us) := by
          exact setIntegral_prod
            ((orderedFinSimplexHeadTail top n).indicator f) hind
    _ = ∫ t in Set.Icc (0 : ℝ) top,
        ∫ us in orderedFinSimplexWithTop t n, f (t, us) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro t ht
          have hfiber :
              (fun us : Fin n → ℝ =>
                  (orderedFinSimplexHeadTail top n).indicator f (t, us)) =
                (orderedFinSimplexWithTop t n).indicator
                  (fun us : Fin n → ℝ => f (t, us)) := by
            funext us
            have hmem :
                (t, us) ∈ orderedFinSimplexHeadTail top n ↔
                  us ∈ orderedFinSimplexWithTop t n := by
              constructor
              · intro hus
                exact hus.2
              · intro hus
                exact ⟨ht, hus⟩
            by_cases hus : us ∈ orderedFinSimplexWithTop t n
            · have hhead : (t, us) ∈ orderedFinSimplexHeadTail top n :=
                hmem.mpr hus
              simp [Set.indicator_of_mem hhead, Set.indicator_of_mem hus]
            · have hhead : (t, us) ∉ orderedFinSimplexHeadTail top n := by
                intro h
                exact hus (hmem.mp h)
              simp [Set.indicator_of_notMem hhead, Set.indicator_of_notMem hus]
          change (∫ us in (Set.univ : Set (Fin n → ℝ)),
              (orderedFinSimplexHeadTail top n).indicator f (t, us)) =
            ∫ us in orderedFinSimplexWithTop t n, f (t, us)
          rw [setIntegral_univ, hfiber,
            integral_indicator (measurableSet_orderedFinSimplexWithTop t n)]

omit [Fintype V] [DecidableEq V] in
/-- At coordinate `0`, the inverse head-tail split is just `Fin.cons`. -/
theorem piFinSuccAbove_zero_symm_apply
    {n : ℕ} (t : ℝ) (us : Fin n → ℝ) :
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).symm (t, us) =
      Fin.cons t us := by
  ext i
  cases i using Fin.cases with
  | zero =>
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv]
  | succ i =>
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv]

omit [Fintype V] [DecidableEq V] in
/--
Fubini split for the finite ordered simplex in `(n+1)` coordinates.
-/
theorem setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_Icc
    (top : ℝ) (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : IntegrableOn f (orderedFinSimplexWithTop top (n + 1))) :
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts =
      ∫ t in Set.Icc (0 : ℝ) top,
        ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by
  let φ : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let g : ℝ × (Fin n → ℝ) → ℝ :=
    fun z => f (φ.symm z)
  have hsector :
      orderedFinSimplexWithTop top (n + 1) =
        φ ⁻¹' orderedFinSimplexHeadTail top n := by
    exact orderedFinSimplexWithTop_succ_eq_piFinSuccAbove_preimage_headTail top n
  have hg : IntegrableOn g (orderedFinSimplexHeadTail top n) := by
    have hcomp :
        IntegrableOn (g ∘ φ) (φ ⁻¹' orderedFinSimplexHeadTail top n) := by
      rw [← hsector]
      refine hf.congr_fun ?_ (measurableSet_orderedFinSimplexWithTop top (n + 1))
      intro ts _hts
      exact congrArg f (φ.left_inv ts).symm
    exact
      ((MeasureTheory.volume_preserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0).integrableOn_comp_preimage
        (MeasurableEquiv.measurableEmbedding φ)
        (f := g)
        (s := orderedFinSimplexHeadTail top n)).mp hcomp
  calc
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts
        = ∫ z in orderedFinSimplexHeadTail top n, g z := by
          exact setIntegral_orderedFinSimplexWithTop_succ_eq_headTail top n f
    _ = ∫ t in Set.Icc (0 : ℝ) top,
          ∫ us in orderedFinSimplexWithTop t n, g (t, us) := by
          exact setIntegral_orderedFinSimplexHeadTail_eq_iterated_Icc top n g hg
    _ = ∫ t in Set.Icc (0 : ℝ) top,
          ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro t _ht
          apply setIntegral_congr_fun (measurableSet_orderedFinSimplexWithTop t n)
          intro us _hus
          dsimp [g, φ]
          congr 1
          ext i
          cases i using Fin.cases with
          | zero =>
              simp [Fin.insertNthEquiv]
          | succ i =>
              simp [Fin.insertNthEquiv]

omit [Fintype V] [DecidableEq V] in
/--
Interval-integral form of the one-step finite ordered-simplex Fubini split.
-/
theorem setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_interval
    {top : ℝ} (htop : 0 ≤ top) (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : IntegrableOn f (orderedFinSimplexWithTop top (n + 1))) :
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts =
      ∫ t in 0..top,
        ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by
  calc
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts
        = ∫ t in Set.Icc (0 : ℝ) top,
            ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by
          exact setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_Icc
            top n f hf
    _ = ∫ t in 0..top,
          ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by
          rw [intervalIntegral.integral_of_le htop]
          rw [setIntegral_congr_set Ioc_ae_eq_Icc]

omit [Fintype V] [DecidableEq V] in
/-- The finite ordered simplex sector in coordinate space is measurable. -/
theorem measurableSet_orderedFinSimplex (n : ℕ) :
    MeasurableSet (orderedFinSimplex n) := by
  have hcube :
      MeasurableSet {ts : Fin n → ℝ | ∀ i, 0 ≤ ts i ∧ ts i ≤ 1} := by
    have hpi : MeasurableSet
        (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Icc
    simpa [Set.pi, Set.mem_Icc] using hpi
  have hsimplex := measurableSet_orderedSimplexParams_ofFn n
  simpa [orderedFinSimplex, Set.ofPred_and] using hcube.inter hsimplex

omit [Fintype V] [DecidableEq V] in
/-- A list of the right length is recovered from its `getD` finite tuple. -/
theorem ofFn_getD_eq_of_length {n : ℕ} (ts : List ℝ)
    (hlen : ts.length = n) :
    List.ofFn (fun i : Fin n => ts.getD i.val 0) = ts := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hofn hts
    rw [List.getElem_ofFn]
    rw [List.getD_eq_getElem]

omit [Fintype V] [DecidableEq V] in
/-- A consed list, read through `getD`, is the corresponding `Fin.cons` tuple. -/
theorem finCons_getD_cons_of_length {n : ℕ} (t : ℝ) (ts : List ℝ)
    (hlen : ts.length = n) :
    (fun i : Fin (n + 1) => (t :: ts).getD i.val 0) =
      Fin.cons t (fun i : Fin n => ts.getD i.val 0) := by
  ext i
  cases i using Fin.cases with
  | zero =>
      simp
  | succ i =>
      change (t :: ts).getD (i.val + 1) 0 = ts.getD i.val 0
      have hidx : i.val + 1 < (t :: ts).length := by
        simp [hlen]
      have htail : i.val < ts.length := by
        simp [hlen]
      rw [List.getD_eq_getElem _ _ hidx]
      rw [List.getD_eq_getElem _ _ htail]
      rfl

/--
For parameter lists of the correct length, `paramsOfOrder` is exactly the
inverse ordered-coordinate map applied to the corresponding `Fin` tuple.
-/
theorem paramsOfOrder_eq_orderMeasurableEquiv_symm_getD_of_length
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ts : List ℝ) (hlen : ts.length = order.length) :
    F.paramsOfOrder order ts =
      (F.orderMeasurableEquivOfOrder horder).symm
        (fun i : Fin order.length => ts.getD i.val 0) := by
  calc
    F.paramsOfOrder order ts
        = F.paramsOfOrder order
            (List.ofFn fun i : Fin order.length => ts.getD i.val 0) := by
          rw [ofFn_getD_eq_of_length ts hlen]
    _ = (F.orderMeasurableEquivOfOrder horder).symm
          (fun i : Fin order.length => ts.getD i.val 0) := by
          exact F.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm horder
            (fun i : Fin order.length => ts.getD i.val 0)

/--
Recursive ordered contributions, rewritten with the same finite coordinates
used on the cube-sector side.
-/
theorem orderedContribution_eq_orderedSimplexIntegral_orderMeasurableEquiv_symm
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedContribution order ρ =
      orderedSimplexIntegral order
        (fun ts =>
          mixedPartialList order.reverse ρ
            (F.standardInterp
              ((F.orderMeasurableEquivOfOrder horder).symm
                (fun i : Fin order.length => ts.getD i.val 0)))) := by
  rw [orderedContribution]
  apply orderedSimplexIntegral_congr_of_length
  intro ts hlen
  rw [F.paramsOfOrder_eq_orderMeasurableEquiv_symm_getD_of_length horder ts hlen]

/--
Measure transport for arbitrary canonical orders, now for integrands written
on forest cube coordinates. This is the sector-side form needed by the final
simplex-sector conversion theorem.
-/
theorem setIntegral_orderedCubeSimplex_eq_orderedFinSimplex_symm
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (g : (F.EdgeParam → ℝ) → ℝ) :
    ∫ u in F.orderedCubeSimplex order, g u
        ∂(volume : Measure (F.EdgeParam → ℝ)) =
      ∫ ts in orderedFinSimplex order.length,
        g ((F.orderMeasurableEquivOfOrder horder).symm ts) := by
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (Fin order.length → ℝ) :=
    F.orderMeasurableEquivOfOrder horder
  have hsector :
      F.orderedCubeSimplex order = φ ⁻¹' orderedFinSimplex order.length := by
    exact F.orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
      horder
  rw [hsector]
  have hpre :=
    (F.measurePreserving_orderMeasurableEquivOfOrder horder).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding φ)
      (fun ts : Fin order.length → ℝ => g (φ.symm ts))
      (orderedFinSimplex order.length)
  have hmeas : MeasurableSet (φ ⁻¹' orderedFinSimplex order.length) := by
    rw [← hsector]
    exact F.measurableSet_orderedCubeSimplex order
  have hcongr :
      ∫ u in φ ⁻¹' orderedFinSimplex order.length, g u
          ∂(volume : Measure (F.EdgeParam → ℝ)) =
        ∫ u in φ ⁻¹' orderedFinSimplex order.length, g (φ.symm (φ u))
          ∂(volume : Measure (F.EdgeParam → ℝ)) := by
    apply setIntegral_congr_fun hmeas
    intro u _hu
    exact congrArg g (φ.left_inv u).symm
  exact hcongr.trans hpre

/-- Arbitrary-order cube-sector contribution in finite ordered coordinates. -/
theorem orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedCubeSectorContribution order ρ =
      ∫ ts in orderedFinSimplex order.length,
        mixedPartialList order.reverse ρ
          (F.standardInterp
            ((F.orderMeasurableEquivOfOrder horder).symm ts)) := by
  rw [orderedCubeSectorContribution]
  exact F.setIntegral_orderedCubeSimplex_eq_orderedFinSimplex_symm horder
    (fun u => mixedPartialList order.reverse ρ (F.standardInterp u))

/--
The actual BKAR sector integrand is integrable on the finite ordered simplex
under the global smoothness hypothesis.
-/
theorem integrableOn_orderedFinSimplex_orderedCubeSectorIntegrand
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    IntegrableOn
      (fun ts : Fin order.length → ℝ =>
        mixedPartialList order.reverse ρ
          (F.standardInterp
            ((F.orderMeasurableEquivOfOrder horder).symm ts)))
      (orderedFinSimplex order.length) := by
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (Fin order.length → ℝ) :=
    F.orderMeasurableEquivOfOrder horder
  let H : (F.EdgeParam → ℝ) → ℝ :=
    fun u => mixedPartialList order.reverse ρ (F.standardInterp u)
  have hsector :
      F.orderedCubeSimplex order = φ ⁻¹' orderedFinSimplex order.length := by
    exact F.orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
      horder
  have hH_unit : IntegrableOn H F.unitCube :=
    F.integrableOn_orderedCubeSectorIntegrand order ρ hρ
  have hH_pre : IntegrableOn H (φ ⁻¹' orderedFinSimplex order.length) := by
    rw [← hsector]
    exact hH_unit.mono_set (F.orderedCubeSimplex_subset_unitCube order)
  have hmeas : MeasurableSet (φ ⁻¹' orderedFinSimplex order.length) := by
    rw [← hsector]
    exact F.measurableSet_orderedCubeSimplex order
  have hcomp :
      IntegrableOn ((fun ts : Fin order.length → ℝ => H (φ.symm ts)) ∘ φ)
        (φ ⁻¹' orderedFinSimplex order.length) := by
    refine hH_pre.congr_fun ?_ hmeas
    intro u _hu
    exact congrArg H (φ.left_inv u).symm
  exact
    ((F.measurePreserving_orderMeasurableEquivOfOrder horder).integrableOn_comp_preimage
      (MeasurableEquiv.measurableEmbedding φ)
      (f := fun ts : Fin order.length → ℝ => H (φ.symm ts))
      (s := orderedFinSimplex order.length)).mp hcomp

omit [Fintype V] in
omit [DecidableEq V] in
/--
Finite-dimensional analytic core of the simplex-sector conversion: for
continuous integrands, the recursive
ordered simplex integral is the set integral over the closed finite ordered
simplex with the same top bound.
-/
theorem orderedSimplexIntegralAux_eq_setIntegral_orderedFinSimplexWithTop_of_continuous
    {top : ℝ} (htop : 0 ≤ top) :
    ∀ (order : List (Edge V)) (G : (Fin order.length → ℝ) → ℝ),
      Continuous G →
        orderedSimplexIntegralAux top order
          (fun ts => G (fun i : Fin order.length => ts.getD i.val 0)) =
        ∫ xs in orderedFinSimplexWithTop top order.length, G xs
  | [], G, _hG => by
      rw [orderedSimplexIntegralAux_nil]
      change
        G (fun i : Fin 0 => ([] : List ℝ).getD i.val 0) =
          ∫ xs in orderedFinSimplexWithTop top 0, G xs
      have hleft :
          (fun i : Fin 0 => ([] : List ℝ).getD i.val 0) =
            (default : Fin 0 → ℝ) :=
        Subsingleton.elim _ _
      rw [hleft]
      have hset : orderedFinSimplexWithTop top 0 = Set.univ := by
        ext xs
        simp [orderedFinSimplexWithTop]
      rw [hset, setIntegral_univ]
      change G (fun _ : Fin 0 => (default : ℝ)) =
        ∫ x, G x ∂(volume : Measure (Fin 0 → ℝ))
      have huniq :=
        MeasureTheory.integral_unique
          (μ := (volume : Measure (Fin 0 → ℝ)))
          (fun y : Fin 0 → ℝ => G y)
      have huniqEq := by
        simpa [Measure.real, volume_pi, Measure.pi_of_empty] using huniq.symm
      exact (congrArg G (Subsingleton.elim (fun _ : Fin 0 => (default : ℝ)) _)).trans
        huniqEq
  | e :: order, G, hG => by
      have hfull :
          IntegrableOn G (orderedFinSimplexWithTop top (order.length + 1)) :=
        integrableOn_orderedFinSimplexWithTop_of_continuous hG
      have hset :
          ∫ xs in orderedFinSimplexWithTop top (order.length + 1), G xs =
            ∫ t in 0..top,
              ∫ us in orderedFinSimplexWithTop t order.length, G (Fin.cons t us) :=
        setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_interval
          htop order.length G hfull
      rw [orderedSimplexIntegralAux_cons]
      calc
        ∫ t in 0..top,
            orderedSimplexIntegralAux t order
              (fun ts =>
                G (fun i : Fin (e :: order).length => (t :: ts).getD i.val 0))
            =
          ∫ t in 0..top,
            ∫ us in orderedFinSimplexWithTop t order.length, G (Fin.cons t us) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have htIcc : t ∈ Set.Icc (0 : ℝ) top := by
              simpa [Set.uIcc_of_le htop] using ht
            let Gt : (Fin order.length → ℝ) → ℝ :=
              fun us => G (Fin.cons t us)
            have hGt : Continuous Gt := by
              exact hG.comp
                ((continuous_const : Continuous fun _ : Fin order.length → ℝ => t).finCons
                  continuous_id)
            calc
              orderedSimplexIntegralAux t order
                  (fun ts =>
                    G (fun i : Fin (e :: order).length => (t :: ts).getD i.val 0))
                  =
                orderedSimplexIntegralAux t order
                  (fun ts => Gt (fun i : Fin order.length => ts.getD i.val 0)) := by
                  apply orderedSimplexIntegralAux_congr_of_length
                  intro ts hlen
                  dsimp [Gt]
                  congr 1
                  simpa using finCons_getD_cons_of_length t ts hlen
              _ = ∫ us in orderedFinSimplexWithTop t order.length, Gt us := by
                  exact
                    orderedSimplexIntegralAux_eq_setIntegral_orderedFinSimplexWithTop_of_continuous
                      htIcc.1 order Gt hGt
              _ = ∫ us in orderedFinSimplexWithTop t order.length, G (Fin.cons t us) := rfl
        _ = ∫ xs in orderedFinSimplexWithTop top (order.length + 1), G xs := hset.symm

omit [Fintype V] [DecidableEq V] in
/-- Unit-bound finite-dimensional analytic core of the simplex-sector conversion. -/
theorem orderedSimplexIntegral_eq_setIntegral_orderedFinSimplex_of_continuous
    (order : List (Edge V)) (G : (Fin order.length → ℝ) → ℝ)
    (hG : Continuous G) :
    orderedSimplexIntegral order
      (fun ts => G (fun i : Fin order.length => ts.getD i.val 0)) =
      ∫ xs in orderedFinSimplex order.length, G xs := by
  classical
  rw [orderedSimplexIntegral]
  calc
    orderedSimplexIntegralAux 1 order
        (fun ts => G (fun i : Fin order.length => ts.getD i.val 0)) =
      ∫ xs in orderedFinSimplexWithTop 1 order.length, G xs := by
        exact
          orderedSimplexIntegralAux_eq_setIntegral_orderedFinSimplexWithTop_of_continuous
            zero_le_one order G hG
    _ = ∫ xs in orderedFinSimplex order.length, G xs := by
        rw [orderedFinSimplex_eq_orderedFinSimplexWithTop_one]

/--
Arbitrary finite-order simplex-sector conversion: under the global BKAR
smoothness hypothesis,
the recursive ordered contribution equals the corresponding closed ordered
cube-sector contribution.
-/
theorem orderedContribution_eq_orderedCubeSectorContribution_of_contDiff
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    F.orderedContribution order ρ =
      F.orderedCubeSectorContribution order ρ := by
  let G : (Fin order.length → ℝ) → ℝ :=
    fun ts =>
      mixedPartialList order.reverse ρ
        (F.standardInterp
          ((F.orderMeasurableEquivOfOrder horder).symm ts))
  have hG : Continuous G := by
    have hcoords :
        Continuous
          (fun ts : Fin order.length → ℝ =>
            (F.orderMeasurableEquivOfOrder horder).symm ts) :=
      F.continuous_orderMeasurableEquivOfOrder_symm horder
    exact (hρ.mixedPartialList_continuous order.reverse).comp
      (F.standardInterp_continuous_comp hcoords)
  calc
    F.orderedContribution order ρ =
      orderedSimplexIntegral order
        (fun ts => G (fun i : Fin order.length => ts.getD i.val 0)) := by
        exact F.orderedContribution_eq_orderedSimplexIntegral_orderMeasurableEquiv_symm
          horder ρ
    _ = ∫ xs in orderedFinSimplex order.length, G xs := by
        exact orderedSimplexIntegral_eq_setIntegral_orderedFinSimplex_of_continuous
          order G hG
    _ = F.orderedCubeSectorContribution order ρ := by
        exact (F.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral horder ρ).symm

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
