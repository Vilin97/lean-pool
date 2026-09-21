/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Two-function median

A standalone measure-theory prelude.  For a finite measure `μ` on `α` and two
almost-everywhere measurable real functions `f g`, there is a real level `m`
such that both the total upper mass and the total lower mass of the pair `(f, g)`
across the *two* copies of `α` stay below `μ univ`:

`μ {m < f} + μ {m < g} ≤ μ univ`  and  `μ {f < m} + μ {g < m} ≤ μ univ`.

This is exactly the statement that `m` is a median of the combined function on the
disjoint union of two copies of `α`, phrased without sum types.

No `sorry`, no axioms, no heartbeat overrides.
-/

namespace Homogenization

open MeasureTheory Filter Topology Set

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Two-function median.**  For a finite measure and two
a.e.-measurable real functions, there is a common level `m` at which the combined
upper mass and the combined lower mass are each at most the total mass. -/
theorem exists_two_function_median [IsFiniteMeasure μ]
    {f g : α → ℝ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∃ m : ℝ,
      μ {x | m < f x} + μ {x | m < g x} ≤ μ Set.univ ∧
      μ {x | f x < m} + μ {x | g x < m} ≤ μ Set.univ := by
  classical
  have hμfin : μ Set.univ ≠ ⊤ := measure_ne_top μ _
  -- null-measurability of the strict upper level sets
  have hNMf : ∀ t : ℝ, NullMeasurableSet {x | t < f x} μ := fun t =>
    nullMeasurableSet_lt aemeasurable_const hf
  have hNMg : ∀ t : ℝ, NullMeasurableSet {x | t < g x} μ := fun t =>
    nullMeasurableSet_lt aemeasurable_const hg
  -- antitonicity of the combined "upper mass"
  have hUanti : ∀ {s t : ℝ}, s ≤ t →
      μ {x | t < f x} + μ {x | t < g x} ≤ μ {x | s < f x} + μ {x | s < g x} := by
    intro s t hst
    exact add_le_add
      (measure_mono fun x hx => lt_of_le_of_lt hst hx)
      (measure_mono fun x hx => lt_of_le_of_lt hst hx)
  -- Trivial case: the total mass vanishes.
  rcases eq_or_ne (μ Set.univ) 0 with hzero | hpos0
  · have hz : ∀ s : Set α, μ s = 0 := fun s => measure_mono_null (Set.subset_univ s) hzero
    exact ⟨0, by simp [hz], by simp [hz]⟩
  have hpos : 0 < μ Set.univ := zero_lt_iff.mpr hpos0
  -- The lower-mass control: whenever the upper mass at `t` reaches the total mass,
  -- the lower mass at `t` stays below it.
  have hLowerMass : ∀ t : ℝ,
      μ Set.univ ≤ μ {x | t < f x} + μ {x | t < g x} →
      μ {x | f x < t} + μ {x | g x < t} ≤ μ Set.univ := by
    intro t hle
    have hcf : μ {x | t < f x} + μ {x | t < f x}ᶜ = μ Set.univ :=
      measure_add_measure_compl₀ (hNMf t)
    have hcg : μ {x | t < g x} + μ {x | t < g x}ᶜ = μ Set.univ :=
      measure_add_measure_compl₀ (hNMg t)
    have hsubf : {x | f x < t} ⊆ {x | t < f x}ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
      exact hx.le
    have hsubg : {x | g x < t} ⊆ {x | t < g x}ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
      exact hx.le
    have hUt_ne : μ {x | t < f x} + μ {x | t < g x} ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩
    have hrearrange :
        (μ {x | t < f x}ᶜ + μ {x | t < g x}ᶜ) + (μ {x | t < f x} + μ {x | t < g x})
          = (μ {x | t < f x} + μ {x | t < f x}ᶜ) + (μ {x | t < g x} + μ {x | t < g x}ᶜ) := by
      ring
    have hsum :
        (μ {x | t < f x}ᶜ + μ {x | t < g x}ᶜ) + (μ {x | t < f x} + μ {x | t < g x})
          = μ Set.univ + μ Set.univ := by
      rw [hrearrange, hcf, hcg]
    have hXle : μ {x | t < f x}ᶜ + μ {x | t < g x}ᶜ ≤ μ Set.univ := by
      rw [← ENNReal.add_le_add_iff_right hUt_ne, hsum]
      exact add_le_add le_rfl hle
    calc
      μ {x | f x < t} + μ {x | g x < t}
          ≤ μ {x | t < f x}ᶜ + μ {x | t < g x}ᶜ :=
            add_le_add (measure_mono hsubf) (measure_mono hsubg)
      _ ≤ μ Set.univ := hXle
  -- The candidate set of levels whose upper mass is already at most the total mass.
  set S : Set ℝ :=
    {t : ℝ | μ {x | t < f x} + μ {x | t < g x} ≤ μ Set.univ} with hSdef
  have hmemS : ∀ t : ℝ,
      (t ∈ S ↔ μ {x | t < f x} + μ {x | t < g x} ≤ μ Set.univ) := by
    intro t; rw [hSdef]; exact Iff.rfl
  have hSupClosed : ∀ {s t : ℝ}, s ∈ S → s ≤ t → t ∈ S := by
    intro s t hs hst
    rw [hmemS] at hs ⊢
    exact le_trans (hUanti hst) hs
  -- `S` is nonempty: the upper mass tends to `0` as the level tends to `+∞`.
  have hSne : S.Nonempty := by
    have hInterEmptyF : ⋂ n : ℕ, {x | (n : ℝ) < f x} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Set.mem_iInter] at hx
      obtain ⟨n, hn⟩ := exists_nat_gt (f x)
      exact absurd (hx n) (not_lt.mpr hn.le)
    have hInterEmptyG : ⋂ n : ℕ, {x | (n : ℝ) < g x} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Set.mem_iInter] at hx
      obtain ⟨n, hn⟩ := exists_nat_gt (g x)
      exact absurd (hx n) (not_lt.mpr hn.le)
    have hAntiF : Antitone (fun n : ℕ => {x | (n : ℝ) < f x}) := by
      intro a b hab x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have hAntiG : Antitone (fun n : ℕ => {x | (n : ℝ) < g x}) := by
      intro a b hab x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have htf : Tendsto (fun n : ℕ => μ {x | (n : ℝ) < f x}) atTop (𝓝 0) := by
      have hconv := tendsto_measure_iInter_atTop (μ := μ)
        (s := fun n : ℕ => {x | (n : ℝ) < f x}) (fun n => hNMf _) hAntiF
        ⟨0, measure_ne_top μ _⟩
      rwa [hInterEmptyF, measure_empty] at hconv
    have htg : Tendsto (fun n : ℕ => μ {x | (n : ℝ) < g x}) atTop (𝓝 0) := by
      have hconv := tendsto_measure_iInter_atTop (μ := μ)
        (s := fun n : ℕ => {x | (n : ℝ) < g x}) (fun n => hNMg _) hAntiG
        ⟨0, measure_ne_top μ _⟩
      rwa [hInterEmptyG, measure_empty] at hconv
    have htU : Tendsto (fun n : ℕ => μ {x | (n : ℝ) < f x} + μ {x | (n : ℝ) < g x})
        atTop (𝓝 0) := by simpa using htf.add htg
    obtain ⟨n, hn⟩ := (htU.eventually_lt_const hpos).exists
    exact ⟨(n : ℝ), (hmemS _).mpr hn.le⟩
  -- `S` is bounded below: the upper mass tends to `2 μ univ > μ univ` as the level
  -- tends to `-∞`.
  have hbdd : BddBelow S := by
    have hUnionUnivF : ⋃ n : ℕ, {x | -(n : ℝ) < f x} = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x
      rw [Set.mem_iUnion]
      obtain ⟨n, hn⟩ := exists_nat_gt (-(f x))
      exact ⟨n, by simp only [Set.mem_ofPred_eq]; linarith⟩
    have hUnionUnivG : ⋃ n : ℕ, {x | -(n : ℝ) < g x} = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x
      rw [Set.mem_iUnion]
      obtain ⟨n, hn⟩ := exists_nat_gt (-(g x))
      exact ⟨n, by simp only [Set.mem_ofPred_eq]; linarith⟩
    have hmonoF : Monotone (fun n : ℕ => {x | -(n : ℝ) < f x}) := by
      intro a b hab x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      have : -(b : ℝ) ≤ -(a : ℝ) := by
        have : (a : ℝ) ≤ b := by exact_mod_cast hab
        linarith
      linarith
    have hmonoG : Monotone (fun n : ℕ => {x | -(n : ℝ) < g x}) := by
      intro a b hab x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      have : -(b : ℝ) ≤ -(a : ℝ) := by
        have : (a : ℝ) ≤ b := by exact_mod_cast hab
        linarith
      linarith
    have htf : Tendsto (fun n : ℕ => μ {x | -(n : ℝ) < f x}) atTop (𝓝 (μ Set.univ)) := by
      have hconv := tendsto_measure_iUnion_atTop (μ := μ) hmonoF
      rwa [hUnionUnivF] at hconv
    have htg : Tendsto (fun n : ℕ => μ {x | -(n : ℝ) < g x}) atTop (𝓝 (μ Set.univ)) := by
      have hconv := tendsto_measure_iUnion_atTop (μ := μ) hmonoG
      rwa [hUnionUnivG] at hconv
    have h2 : Tendsto (fun n : ℕ => μ {x | -(n : ℝ) < f x} + μ {x | -(n : ℝ) < g x})
        atTop (𝓝 (μ Set.univ + μ Set.univ)) := htf.add htg
    have hlt : μ Set.univ < μ Set.univ + μ Set.univ := ENNReal.lt_add_right hμfin hpos0
    obtain ⟨n, hn⟩ := (h2.eventually (Ioi_mem_nhds hlt)).exists
    refine ⟨-(n : ℝ), ?_⟩
    intro t ht
    by_contra hcon
    push Not at hcon
    rw [hmemS] at ht
    have hcmp := hUanti hcon.le
    exact absurd (lt_of_lt_of_le hn (le_trans hcmp ht)) (lt_irrefl _)
  -- The median: the infimum of the candidate set.
  set m : ℝ := sInf S with hmdef
  -- Any level strictly above `m` already lies in `S`.
  have hAbove : ∀ t : ℝ, m < t → t ∈ S := by
    intro t hmt
    obtain ⟨s, hsS, hst⟩ := exists_lt_of_csInf_lt hSne (hmdef ▸ hmt)
    exact hSupClosed hsS hst.le
  -- Any level strictly below `m` has upper mass exceeding the total mass.
  have hBelow : ∀ t : ℝ, t < m →
      μ Set.univ < μ {x | t < f x} + μ {x | t < g x} := by
    intro t htm
    have htnotin : t ∉ S := by
      intro htS
      have hle : m ≤ t := by rw [hmdef]; exact csInf_le hbdd htS
      exact absurd (lt_of_lt_of_le htm hle) (lt_irrefl _)
    rw [hmemS] at htnotin
    exact not_le.mp htnotin
  -- Continuity-from-below scaffolding for the two-sided limits at `m`.
  have hUnionUpper : ∀ h : α → ℝ,
      (⋃ k : ℕ, {x | m + 1 / ((k : ℝ) + 1) < h x}) = {x | m < h x} := by
    intro h
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk⟩
      have hpk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨k, by linarith⟩
  have hMonoUpper : ∀ h : α → ℝ,
      Monotone (fun k : ℕ => {x | m + 1 / ((k : ℝ) + 1) < h x}) := by
    intro h a b hab x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hle : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have : (a : ℝ) ≤ b := by exact_mod_cast hab
        linarith
    linarith
  have hUnionLower : ∀ h : α → ℝ,
      (⋃ k : ℕ, {x | h x < m - 1 / ((k : ℝ) + 1)}) = {x | h x < m} := by
    intro h
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk⟩
      have hpk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨k, by linarith⟩
  have hMonoLower : ∀ h : α → ℝ,
      Monotone (fun k : ℕ => {x | h x < m - 1 / ((k : ℝ) + 1)}) := by
    intro h a b hab x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hle : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have : (a : ℝ) ≤ b := by exact_mod_cast hab
        linarith
    linarith
  refine ⟨m, ?_, ?_⟩
  · -- Upper condition at `m`.
    have htf := tendsto_measure_iUnion_atTop (μ := μ) (hMonoUpper f)
    have htg := tendsto_measure_iUnion_atTop (μ := μ) (hMonoUpper g)
    rw [hUnionUpper f] at htf
    rw [hUnionUpper g] at htg
    refine le_of_tendsto' (htf.add htg) (fun k => ?_)
    have hin : m + 1 / ((k : ℝ) + 1) ∈ S :=
      hAbove _ (lt_add_of_pos_right m (by positivity))
    rw [hmemS] at hin
    exact hin
  · -- Lower condition at `m`.
    have htf := tendsto_measure_iUnion_atTop (μ := μ) (hMonoLower f)
    have htg := tendsto_measure_iUnion_atTop (μ := μ) (hMonoLower g)
    rw [hUnionLower f] at htf
    rw [hUnionLower g] at htg
    refine le_of_tendsto' (htf.add htg) (fun k => ?_)
    have hlt : m - 1 / ((k : ℝ) + 1) < m := by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    exact hLowerMass _ (hBelow _ hlt).le

end Homogenization
