/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Integration of Lower Semianalytic Functions along Borel Kernels

  **Bertsekas–Shreve, Proposition 7.48** — now a THEOREM (formerly an axiom):
  if f : X × Y → ℝ≥0∞ is lower semianalytic and κ is a Borel-measurable
  stochastic kernel, then x ↦ ∫⁻ y, f (x, y) ∂(κ x) is lower semianalytic.

  Proof architecture (BS pp. 180–181):
  1. Epigraph trick: E_n = {(x, y, b) | f (x,y) ≤ ofReal b, b ∈ [0, n]} is
     analytic in X × (Y × ℝ).
  2. Fubini for null-measurable sets (via universal measurability of
     analytic sets, `AnalyticSet.nullMeasurableSet`):
     (κ x ⊗ λ)((E_n)_x) = n − ∫⁻ min (f (x,·)) n dκ x.
  3. Parametrized Choquet capacitability (`AnalyticSet.kernel_section_gt`):
     x ↦ (κ x ⊗ λ)((E_n)_x) is upper semianalytic.
  4. Truncation limit n → ∞ and countable rational bookkeeping.
-/
module

public import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.Capacitability
public import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.LowerSemianalytic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub


/-! ## Binary closure properties of analytic sets -/

@[expose] public section

open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section



theorem MeasureTheory.AnalyticSet.inter'
    {W : Type*} [TopologicalSpace W] [T2Space W]
    {S T : Set W} (hS : AnalyticSet S) (hT : AnalyticSet T) :
    AnalyticSet (S ∩ T) := by
  have h : S ∩ T = ⋂ b : Bool, (bif b then S else T) := by
    ext w; simp [Bool.forall_bool, and_comm]
  rw [h]
  exact AnalyticSet.iInter fun b => by cases b <;> simpa

theorem MeasureTheory.AnalyticSet.union'
    {W : Type*} [TopologicalSpace W]
    {S T : Set W} (hS : AnalyticSet S) (hT : AnalyticSet T) :
    AnalyticSet (S ∪ T) := by
  have h : S ∪ T = ⋃ b : Bool, (bif b then S else T) := by
    ext w; simp [Bool.exists_bool, or_comm]
  rw [h]
  exact AnalyticSet.iUnion fun b => by cases b <;> simpa

/-- Preimages of analytic sets under continuous maps from Polish spaces
    are analytic (graph trick: the graph relation is closed, hence analytic,
    and the preimage is its first-coordinate projection). -/
theorem MeasureTheory.AnalyticSet.preimage_of_continuous
    {W V : Type*} [TopologicalSpace W] [PolishSpace W]
    [TopologicalSpace V] [T2Space V]
    {S : Set V} (hS : AnalyticSet S) {h : W → V} (hh : Continuous h) :
    AnalyticSet (h ⁻¹' S) := by
  rw [AnalyticSet] at hS
  rcases hS with rfl | ⟨g, hg_cont, hg_range⟩
  · rw [preimage_empty]; exact analyticSet_empty
  have hpre : h ⁻¹' range g = Prod.fst '' {p : W × (ℕ → ℕ) | g p.2 = h p.1} := by
    ext w
    simp only [mem_preimage, mem_range, mem_image, Prod.exists, mem_ofPred_eq]
    constructor
    · rintro ⟨σ, hσ⟩; exact ⟨w, σ, hσ, rfl⟩
    · rintro ⟨w', σ, hgσ, rfl⟩; exact ⟨σ, hgσ⟩
  rw [← hg_range, hpre]
  refine AnalyticSet.image_of_continuous ?_ continuous_fst
  exact (isClosed_eq (hg_cont.comp continuous_snd)
    (hh.comp continuous_fst)).analyticSet

/-! ## ENNReal bookkeeping -/

theorem ennreal_le_iff_forall_lt_add_inv {a q : ℝ≥0∞} (hq : q ≠ ∞) :
    a ≤ q ↔ ∀ k : ℕ, a < q + ((k : ℝ≥0∞) + 1)⁻¹ := by
  constructor
  · intro h k
    exact lt_of_le_of_lt h
      (ENNReal.lt_add_right hq (ENNReal.inv_ne_zero.mpr (by finiteness)))
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨ε, hε0, hεa⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hlt
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt
      (show (ε : ℝ≥0∞) ≠ 0 from by exact_mod_cast hε0.ne')
    have h1 : ((k : ℝ≥0∞) + 1)⁻¹ ≤ (ε : ℝ≥0∞) :=
      le_of_lt (lt_of_le_of_lt (ENNReal.inv_le_inv.mpr le_self_add) hk)
    exact absurd (h k) (not_lt.mpr (le_trans (by gcongr) hεa.le))

theorem ennreal_iSup_min_natCast (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  rcases eq_or_ne a ∞ with rfl | ha
  · have hmin : ∀ n : ℕ, min (∞ : ℝ≥0∞) (n : ℝ≥0∞) = (n : ℝ≥0∞) :=
      fun n => min_eq_right le_top
    calc (∞ : ℝ≥0∞) = ⨆ n : ℕ, (n : ℝ≥0∞) := ENNReal.iSup_natCast.symm
      _ ≤ ⨆ n : ℕ, min (∞ : ℝ≥0∞) (n : ℝ≥0∞) :=
          iSup_mono fun n => (hmin n).symm.le
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le n (by simp [min_eq_left hn.le])

/-! ## AEMeasurability from analytic sublevel sets

Combines the universal measurability of analytic sets (Part VI of
Capacitability.lean) with the Borel generation of `ℝ≥0∞` by rays. -/

theorem aemeasurable_of_analytic_sublevels
    {V : Type*} [TopologicalSpace V] [PolishSpace V]
    [MeasurableSpace V] [BorelSpace V] {g : V → ℝ≥0∞}
    (hg : ∀ c, AnalyticSet {v | g v < c})
    (μ : Measure V) [IsFiniteMeasure μ] :
    AEMeasurable g μ := by
  have hnm : NullMeasurable g μ := by
    intro s hs
    rw [BorelSpace.measurable_eq (α := ℝ≥0∞),
      borel_eq_generateFrom_Iio ℝ≥0∞] at hs
    induction hs with
    | basic u hu =>
      obtain ⟨c, rfl⟩ := hu
      have hpre : g ⁻¹' Iio c = {v | g v < c} := rfl
      rw [hpre]
      exact (hg c).nullMeasurableSet μ
    | empty =>
      rw [preimage_empty]
      exact MeasurableSet.empty.nullMeasurableSet
    | compl u _ ih =>
      rw [preimage_compl]
      exact ih.compl
    | iUnion u _ ih =>
      rw [preimage_iUnion]
      exact NullMeasurableSet.iUnion ih
  exact hnm.aemeasurable

/-! ## Fubini for analytic sets (null-measurable version) -/

/-- For an analytic `S` in a product of Polish spaces and finite Borel
    measures, the product (outer) measure of `S` is the integral of the
    (outer) measures of its sections. Uses universal measurability. -/
theorem MeasureTheory.AnalyticSet.prod_apply
    {V W : Type*} [TopologicalSpace V] [PolishSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace W] [PolishSpace W]
    [MeasurableSpace W] [BorelSpace W]
    {S : Set (V × W)} (hS : AnalyticSet S)
    (μ : Measure V) [IsFiniteMeasure μ]
    (ν : Measure W) [IsFiniteMeasure ν] :
    μ.prod ν S = ∫⁻ v, ν (Prod.mk v ⁻¹' S) ∂μ := by
  obtain ⟨B, hBmeas, haeq⟩ := hS.nullMeasurableSet (μ.prod ν)
  have h1 : μ.prod ν S = μ.prod ν B := measure_congr haeq
  have hSB : μ.prod ν (S \ B) = 0 := ae_le_set.mp haeq.le
  have hBS : μ.prod ν (B \ S) = 0 := ae_le_set.mp haeq.symm.le
  -- measurable hulls of the two null differences
  set N₁ := toMeasurable (μ.prod ν) (S \ B) with hN₁
  set N₂ := toMeasurable (μ.prod ν) (B \ S) with hN₂
  have hN₁meas : MeasurableSet N₁ := measurableSet_toMeasurable _ _
  have hN₂meas : MeasurableSet N₂ := measurableSet_toMeasurable _ _
  have hN₁null : μ.prod ν N₁ = 0 := by rw [hN₁, measure_toMeasurable]; exact hSB
  have hN₂null : μ.prod ν N₂ = 0 := by rw [hN₂, measure_toMeasurable]; exact hBS
  -- a.e. sections of the hulls are ν-null
  have hsec : ∀ (N : Set (V × W)), MeasurableSet N → μ.prod ν N = 0 →
      ∀ᵐ v ∂μ, ν (Prod.mk v ⁻¹' N) = 0 := by
    intro N hNmeas hNnull
    have hint := (Measure.prod_apply hNmeas).symm.trans hNnull
    exact (lintegral_eq_zero_iff (measurable_measure_prodMk_left hNmeas)).mp hint
  have hae : (fun v => ν (Prod.mk v ⁻¹' S)) =ᵐ[μ] fun v => ν (Prod.mk v ⁻¹' B) := by
    filter_upwards [hsec N₁ hN₁meas hN₁null, hsec N₂ hN₂meas hN₂null]
      with v hv1 hv2
    have hsub1 : Prod.mk v ⁻¹' S ⊆ (Prod.mk v ⁻¹' B) ∪ (Prod.mk v ⁻¹' N₁) := by
      intro w hw
      by_cases hwB : w ∈ Prod.mk v ⁻¹' B
      · exact Or.inl hwB
      · exact Or.inr (subset_toMeasurable _ _ ⟨hw, hwB⟩)
    have hsub2 : Prod.mk v ⁻¹' B ⊆ (Prod.mk v ⁻¹' S) ∪ (Prod.mk v ⁻¹' N₂) := by
      intro w hw
      by_cases hwS : w ∈ Prod.mk v ⁻¹' S
      · exact Or.inl hwS
      · exact Or.inr (subset_toMeasurable _ _ ⟨hw, hwS⟩)
    refine le_antisymm ?_ ?_
    · calc ν (Prod.mk v ⁻¹' S)
          ≤ ν ((Prod.mk v ⁻¹' B) ∪ (Prod.mk v ⁻¹' N₁)) := measure_mono hsub1
        _ ≤ ν (Prod.mk v ⁻¹' B) + ν (Prod.mk v ⁻¹' N₁) := measure_union_le _ _
        _ = ν (Prod.mk v ⁻¹' B) := by rw [hv1, add_zero]
    · calc ν (Prod.mk v ⁻¹' B)
          ≤ ν ((Prod.mk v ⁻¹' S) ∪ (Prod.mk v ⁻¹' N₂)) := measure_mono hsub2
        _ ≤ ν (Prod.mk v ⁻¹' S) + ν (Prod.mk v ⁻¹' N₂) := measure_union_le _ _
        _ = ν (Prod.mk v ⁻¹' S) := by rw [hv2, add_zero]
  rw [h1, Measure.prod_apply hBmeas, lintegral_congr_ae hae.symm]

/-! ## The Lebesgue section computation -/

theorem volume_restrict_epigraph_section (t : ℝ≥0∞) (n : ℕ) :
    volume.restrict (Icc (0 : ℝ) n) {b : ℝ | t ≤ ENNReal.ofReal b}
      = (n : ℝ≥0∞) - min t (n : ℝ≥0∞) := by
  rw [Measure.restrict_apply' measurableSet_Icc]
  rcases eq_or_ne t ∞ with rfl | ht
  · have hempty : {b : ℝ | (∞ : ℝ≥0∞) ≤ ENNReal.ofReal b} ∩ Icc (0 : ℝ) n = ∅ := by
      ext b
      simp [top_le_iff, ENNReal.ofReal_ne_top]
    rw [hempty]
    simp
  · have hinter : {b : ℝ | t ≤ ENNReal.ofReal b} ∩ Icc (0 : ℝ) n
        = Icc t.toReal n := by
      ext b
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨(ENNReal.le_ofReal_iff_toReal_le ht h2).mp h1, h3⟩
      · rintro ⟨h1, h2⟩
        have hb0 : (0 : ℝ) ≤ b := le_trans ENNReal.toReal_nonneg h1
        exact ⟨(ENNReal.le_ofReal_iff_toReal_le ht hb0).mpr h1, hb0, h2⟩
    rw [hinter, Real.volume_Icc]
    rcases le_or_gt t (n : ℝ≥0∞) with htn | htn
    · rw [min_eq_left htn, ← ENNReal.ofReal_natCast n,
        ← ENNReal.ofReal_toReal ht,
        ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal ht]
    · have hnt : (n : ℝ) < t.toReal := by
        rw [← ENNReal.toReal_natCast n]
        exact (ENNReal.toReal_lt_toReal (by finiteness) ht).mpr htn
      rw [min_eq_right htn.le, tsub_self,
        ENNReal.ofReal_eq_zero.mpr (by linarith)]

/-! ## The analytic epigraph -/

section Epigraph

variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- Non-strict sublevel sets at finite levels are analytic. -/
theorem IsLowerSemianalytic.analyticSet_le
    {f : X × Y → ℝ≥0∞} (hf : IsLowerSemianalytic (X := X × Y) f)
    {q : ℝ≥0∞} (hq : q ≠ ∞) :
    AnalyticSet {p : X × Y | f p ≤ q} := by
  have heq : {p : X × Y | f p ≤ q}
      = ⋂ k : ℕ, {p | f p < q + ((k : ℝ≥0∞) + 1)⁻¹} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
    exact ennreal_le_iff_forall_lt_add_inv hq
  rw [heq]
  exact AnalyticSet.iInter fun k => hf _

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- The epigraph condition in a real parameter is analytic. -/
theorem IsLowerSemianalytic.analyticSet_epigraph
    {f : X × Y → ℝ≥0∞} (hf : IsLowerSemianalytic (X := X × Y) f) :
    AnalyticSet {pb : (X × Y) × ℝ | f pb.1 ≤ ENNReal.ofReal pb.2} := by
  have heq : {pb : (X × Y) × ℝ | f pb.1 ≤ ENNReal.ofReal pb.2}
      = ⋂ q : ℚ,
          ({pb : (X × Y) × ℝ |
              ENNReal.ofReal pb.2 < (Real.toNNReal q : ℝ≥0∞)}ᶜ
            ∪ (Prod.fst ⁻¹' {p : X × Y | f p ≤ (Real.toNNReal q : ℝ≥0∞)})) := by
    ext ⟨p, b⟩
    simp only [mem_iInter, mem_union, mem_compl_iff, mem_ofPred_eq,
      mem_preimage, not_lt]
    constructor
    · intro h q
      rcases le_or_gt (Real.toNNReal q : ℝ≥0∞) (ENNReal.ofReal b) with hle | hlt
      · exact Or.inl hle
      · exact Or.inr (h.trans hlt.le)
    · intro h
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨q, _, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hcon
      rcases h q with h3 | h3
      · exact absurd h1 (not_lt.mpr h3)
      · exact absurd h2 (not_lt.mpr h3)
  rw [heq]
  refine AnalyticSet.iInter fun q => ?_
  refine AnalyticSet.union' ?_ ?_
  · refine IsClosed.analyticSet ?_
    exact (isOpen_Iio.preimage
      (ENNReal.continuous_ofReal.comp continuous_snd)).isClosed_compl
  · exact (hf.analyticSet_le (by finiteness)).preimage_of_continuous
      continuous_fst

/-! ## The main theorem: BS Proposition 7.48 -/

/-- **Bertsekas–Shreve, Proposition 7.48** (formerly an axiom, now proved):
    integration of a lower semianalytic function along a Borel-measurable
    stochastic kernel is lower semianalytic. -/
theorem lintegral_lowerSemianalytic
    {f : X × Y → ℝ≥0∞} (hf : IsLowerSemianalytic (X := X × Y) f)
    {κ : X → Measure Y} (hκ : Measurable κ)
    (hκp : ∀ x, IsProbabilityMeasure (κ x)) :
    IsLowerSemianalytic (fun x => ∫⁻ y, f (x, y) ∂(κ x)) := by
  -- kernel packaging
  set κK : Kernel X Y := ⟨κ, hκ⟩ with hκK
  have : IsMarkovKernel κK := ⟨fun a => hκp a⟩
  -- transported epigraph pieces Eₙ ⊆ X × (Y × ℝ)
  set E : ℕ → Set (X × (Y × ℝ)) := fun n =>
    (Homeomorph.prodAssoc X Y ℝ).symm ⁻¹'
      ({pb : (X × Y) × ℝ | f pb.1 ≤ ENNReal.ofReal pb.2}
        ∩ ((univ : Set (X × Y)) ×ˢ Icc (0 : ℝ) n)) with hE
  have hE_analytic : ∀ n, AnalyticSet (E n) := by
    intro n
    refine AnalyticSet.preimage_of_continuous ?_ (Homeomorph.continuous _)
    exact hf.analyticSet_epigraph.inter'
      ((MeasurableSet.univ.prod measurableSet_Icc).analyticSet)
  -- double sections of Eₙ are epigraph slices in ℝ
  have hE_sec : ∀ (n : ℕ) (x : X) (y : Y),
      Prod.mk y ⁻¹' (Prod.mk x ⁻¹' E n)
        = {b : ℝ | f (x, y) ≤ ENNReal.ofReal b} ∩ Icc (0 : ℝ) n := by
    intro n x y
    ext b
    simp only [hE, mem_preimage]
    constructor
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, mem_univ _, h2⟩
  -- the Lebesgue factors
  set lam : ℕ → Measure ℝ := fun n => volume.restrict (Icc (0 : ℝ) n) with hlam
  have hlam_fin : ∀ n, IsFiniteMeasure (lam n) := fun n => by
    rw [hlam]; infer_instance
  -- truncated integrals
  set a : ℕ → X → ℝ≥0∞ :=
    fun n x => ∫⁻ y, min (f (x, y)) (n : ℝ≥0∞) ∂(κ x) with ha
  have ha_le : ∀ n x, a n x ≤ (n : ℝ≥0∞) := by
    intro n x
    rw [ha]
    refine le_trans (lintegral_mono fun y => min_le_right _ _) ?_
    rw [lintegral_const, measure_univ, mul_one]
  -- sections of f are AEMeasurable
  have hfx_slev : ∀ (x : X) (c : ℝ≥0∞), AnalyticSet {y | f (x, y) < c} := by
    intro x c
    have hset : {y | f (x, y) < c} = Prod.mk x ⁻¹' {p : X × Y | f p < c} := rfl
    rw [hset]
    exact (hf c).preimage_of_continuous
      (Continuous.prodMk continuous_const continuous_id)
  have hfx_ae : ∀ x : X, AEMeasurable (fun y => f (x, y)) (κ x) := fun x =>
    aemeasurable_of_analytic_sublevels (hfx_slev x) (κ x)
  -- key value identity: (κ x ⊗ λₙ)((Eₙ)_x) = n − aₙ x
  have hval : ∀ (n : ℕ) (x : X),
      (κ x).prod (lam n) (Prod.mk x ⁻¹' E n) = (n : ℝ≥0∞) - a n x := by
    intro n x
    have hsec_analytic : AnalyticSet (Prod.mk x ⁻¹' E n) :=
      (hE_analytic n).preimage_of_continuous
        (Continuous.prodMk continuous_const continuous_id)
    rw [hsec_analytic.prod_apply (κ x) (lam n)]
    have hint : ∀ y : Y, (lam n) (Prod.mk y ⁻¹' (Prod.mk x ⁻¹' E n))
        = (n : ℝ≥0∞) - min (f (x, y)) (n : ℝ≥0∞) := by
      intro y
      rw [hE_sec n x y, hlam]
      have h1 : volume.restrict (Icc (0 : ℝ) n)
            ({b : ℝ | f (x, y) ≤ ENNReal.ofReal b} ∩ Icc (0 : ℝ) n)
          = volume.restrict (Icc (0 : ℝ) n)
            {b : ℝ | f (x, y) ≤ ENNReal.ofReal b} := by
        rw [Measure.restrict_apply' measurableSet_Icc,
          Measure.restrict_apply' measurableSet_Icc, inter_assoc, inter_self]
      rw [h1]
      exact volume_restrict_epigraph_section _ n
    rw [lintegral_congr fun y => hint y]
    have hmin_ae : AEMeasurable (fun y => min (f (x, y)) (n : ℝ≥0∞)) (κ x) :=
      (hfx_ae x).min aemeasurable_const
    have hle : (fun y => min (f (x, y)) (n : ℝ≥0∞)) ≤ᵐ[κ x]
        fun _ => (n : ℝ≥0∞) :=
      Filter.Eventually.of_forall fun y => min_le_right _ _
    have hfin : ∫⁻ y, min (f (x, y)) (n : ℝ≥0∞) ∂(κ x) ≠ ∞ :=
      ne_top_of_le_ne_top (by finiteness) (ha_le n x)
    calc ∫⁻ y, ((n : ℝ≥0∞) - min (f (x, y)) (n : ℝ≥0∞)) ∂(κ x)
        = ∫⁻ y, ((fun _ => (n : ℝ≥0∞)) y
            - (fun y => min (f (x, y)) (n : ℝ≥0∞)) y) ∂(κ x) := rfl
      _ = ∫⁻ _, (n : ℝ≥0∞) ∂(κ x)
            - ∫⁻ y, min (f (x, y)) (n : ℝ≥0∞) ∂(κ x) :=
          lintegral_sub' hmin_ae hfin hle
      _ = (n : ℝ≥0∞) - a n x := by
          rw [lintegral_const, measure_univ, mul_one, ha]
  -- parametrized capacitability: superlevels of x ↦ (κ x ⊗ λₙ)((Eₙ)_x)
  have hkey : ∀ (n : ℕ) (c' : ℝ≥0∞),
      AnalyticSet {x | c' < (κ x).prod (lam n) (Prod.mk x ⁻¹' E n)} := by
    intro n c'
    have happ : ∀ x : X, (κK ×ₖ Kernel.const X (lam n)) x = (κ x).prod (lam n) := by
      intro x
      rw [Kernel.prod_apply, Kernel.const_apply]
      rfl
    have h := (hE_analytic n).kernel_section_gt
      (κK ×ₖ Kernel.const X (lam n)) c'
    simpa only [happ] using h
  -- strict sublevels of the truncated integrals are analytic
  have ha_sublevel : ∀ (n : ℕ) (r : ℝ≥0∞), AnalyticSet {x | a n x < r} := by
    intro n r
    rcases le_or_gt r (n : ℝ≥0∞) with hrn | hrn
    · have heq : {x | a n x < r}
          = {x | (n : ℝ≥0∞) - r < (κ x).prod (lam n) (Prod.mk x ⁻¹' E n)} := by
        ext x
        rw [mem_ofPred_eq, mem_ofPred_eq, hval n x]
        constructor
        · intro h
          rw [ENNReal.sub_lt_iff_lt_right
            (ne_top_of_le_ne_top (by finiteness) hrn) hrn]
          calc (n : ℝ≥0∞) = a n x + ((n : ℝ≥0∞) - a n x) :=
                (add_tsub_cancel_of_le (ha_le n x)).symm
            _ < r + ((n : ℝ≥0∞) - a n x) :=
                ENNReal.add_lt_add_right
                  (ne_top_of_le_ne_top (by finiteness) tsub_le_self) h
            _ = ((n : ℝ≥0∞) - a n x) + r := add_comm _ _
        · intro h
          by_contra hra
          rw [not_lt] at hra
          exact absurd h (not_lt.mpr (tsub_le_tsub_left hra _))
      rw [heq]
      exact hkey n _
    · have heq : {x | a n x < r} = univ :=
        eq_univ_of_forall fun x => lt_of_le_of_lt (ha_le n x) hrn
      rw [heq]
      exact MeasurableSet.univ.analyticSet
  -- the integral is the increasing limit of the truncations
  have hsup : ∀ x : X, (∫⁻ y, f (x, y) ∂(κ x)) = ⨆ n : ℕ, a n x := by
    intro x
    calc ∫⁻ y, f (x, y) ∂(κ x)
        = ∫⁻ y, ⨆ n : ℕ, min (f (x, y)) (n : ℝ≥0∞) ∂(κ x) := by
          congr 1
          funext y
          rw [ennreal_iSup_min_natCast]
      _ = ⨆ n : ℕ, a n x := by
          rw [ha]
          exact lintegral_iSup'
            (fun n => (hfx_ae x).min aemeasurable_const)
            (Filter.Eventually.of_forall fun y n m hnm =>
              min_le_min le_rfl (by exact_mod_cast Nat.cast_le.mpr hnm))
  -- countable rational bookkeeping for the supremum
  intro c
  have hgoal : {x | (∫⁻ y, f (x, y) ∂(κ x)) < c}
      = {x | (⨆ n : ℕ, a n x) < c} := by
    ext x
    rw [mem_ofPred_eq, mem_ofPred_eq, hsup x]
  rw [hgoal]
  have hmain : {x | (⨆ n : ℕ, a n x) < c}
      = ⋃ q : ℚ, {x | (Real.toNNReal q : ℝ≥0∞) < c ∧
          ∀ n : ℕ, a n x ≤ (Real.toNNReal q : ℝ≥0∞)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨q, _, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp h
      exact ⟨q, h2, fun n =>
        le_of_lt (lt_of_le_of_lt (le_iSup (fun m => a m x) n) h1)⟩
    · rintro ⟨q, hqc, hall⟩
      exact lt_of_le_of_lt (iSup_le fun n => hall n) hqc
  rw [hmain]
  refine AnalyticSet.iUnion fun q => ?_
  by_cases hqc : (Real.toNNReal q : ℝ≥0∞) < c
  · have heq : {x | (Real.toNNReal q : ℝ≥0∞) < c ∧
        ∀ n : ℕ, a n x ≤ (Real.toNNReal q : ℝ≥0∞)}
        = ⋂ (n : ℕ) (k : ℕ),
            {x | a n x < (Real.toNNReal q : ℝ≥0∞) + ((k : ℝ≥0∞) + 1)⁻¹} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, hqc, true_and]
      constructor
      · intro h n k
        exact (ennreal_le_iff_forall_lt_add_inv (by finiteness)).mp (h n) k
      · intro h n
        exact (ennreal_le_iff_forall_lt_add_inv (by finiteness)).mpr (h n)
    rw [heq]
    exact AnalyticSet.iInter fun n =>
      AnalyticSet.iInter fun k => ha_sublevel n _
  · have heq : {x | (Real.toNNReal q : ℝ≥0∞) < c ∧
        ∀ n : ℕ, a n x ≤ (Real.toNNReal q : ℝ≥0∞)} = ∅ := by
      ext x
      simp [hqc]
    rw [heq]
    exact analyticSet_empty

end Epigraph

end
