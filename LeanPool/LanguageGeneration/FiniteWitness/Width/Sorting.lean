/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Histories
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.SplitIfs

/-!
# Sorting histories can destroy eventual generation
-/

public section

namespace GenLimit.FiniteWitness.Sorting

/-- The positive natural numbers used for the sorting counterexample. -/
def language : Set ℕ := {n | 0 < n}

/-- Output zero on a sorted sample with a gap, and otherwise output one above its maximum. -/
def output (xs : List ℕ) : ℕ :=
  if xs.Pairwise (· < ·) ∧ xs.toFinset ≠ Finset.Icc 1 (xs.toFinset.sup id) then 0
  else xs.toFinset.sup id + 1

/-- The ordered-history generator implementing the sorting counterexample. -/
def generator : Generic.Generator ℕ := fun _ xs => output (List.ofFn xs)

@[simp] theorem generator_output (stream : ℕ → ℕ) (t : ℕ) :
    Generic.output generator stream t = output (GenLimit.textPrefix stream t) := by
  simp [Generic.output, generator, GenLimit.textPrefix_eq_ofFn]

theorem next_max_good (S : Finset ℕ) : S.sup id + 1 ∈ language ∧ S.sup id + 1 ∉ S := by
  refine ⟨by exact Nat.zero_lt_succ _, ?_⟩
  intro h
  have hh : S.sup id + 1 ≤ S.sup id := Finset.le_sup (f := id) h
  omega

theorem strictMono_of_all_prefixes {stream : ℕ → ℕ}
    (h : ∀ t, (GenLimit.textPrefix stream t).Pairwise (· < ·)) : StrictMono stream := by
  intro i j hij
  have hh := List.pairwise_iff_get.mp (h (j + 1))
    ⟨i, by simp; omega⟩ ⟨j, by simp⟩ (by exact hij)
  simpa [GenLimit.textPrefix, List.get_eq_getElem] using hh

theorem increasing_presented_sample {stream : ℕ → ℕ} (hp : Generic.Presents stream language)
    (hm : StrictMono stream) (t : ℕ) :
    Generic.sample stream t = Finset.Icc 1 ((Generic.sample stream t).sup id) := by
  classical
  let S := Generic.sample stream t
  ext x
  constructor
  · intro hx
    exact Finset.mem_Icc.mpr ⟨Generic.mem_language_of_mem_sample_of_presents hp hx,
      Finset.le_sup (f := id) hx⟩
  · intro hx
    obtain ⟨hxpos, hxmax⟩ := Finset.mem_Icc.mp hx
    have hS : S.Nonempty := by
      by_contra hn
      have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      change x ≤ S.sup id at hxmax
      simp [he] at hxmax
      omega
    obtain ⟨m, hmS, hmmax⟩ := Finset.exists_mem_eq_sup S hS id
    obtain ⟨i, hit, him⟩ := Generic.mem_sample_iff.mp hmS
    have hxL : x ∈ language := hxpos
    obtain ⟨j, hjx⟩ := Set.mem_range.mp (hp.symm ▸ hxL)
    have hjt : j < t := by
      by_contra hn
      have hij : i < j := by omega
      have hh := hm hij
      change x ≤ S.sup id at hxmax
      rw [hmmax] at hxmax
      simp only [id_eq] at hxmax
      rw [him, hjx] at hh
      omega
    exact Generic.mem_sample_iff.mpr ⟨j, hjt, hjx⟩

theorem generator_success : Generic.IsLimitGenerator generator {language} := by
  classical
  intro L hL stream hp
  have he : L = language := hL
  subst L
  by_cases hall : ∀ t, (GenLimit.textPrefix stream t).Pairwise (· < ·)
  · refine ⟨0, ?_⟩
    intro t _
    have hs := increasing_presented_sample hp (strictMono_of_all_prefixes hall) t
    change Generic.output generator stream t ∈ language ∧
      Generic.output generator stream t ∉ Generic.sample stream t
    rw [generator_output, output, ite_eq_right (by
      rintro ⟨_, hne⟩
      exact hne (by simpa only [prefix_toFinset] using hs))]
    simpa only [prefix_toFinset] using next_max_good (Generic.sample stream t)
  · push Not at hall
    obtain ⟨N, hN⟩ := hall
    refine ⟨N, ?_⟩
    intro t ht
    have hn : ¬ (GenLimit.textPrefix stream t).Pairwise (· < ·) := by
      intro h
      exact hN (h.sublist (GenLimit.textPrefix_prefix stream ht).sublist)
    simpa [Generic.CorrectAt, output, hn] using next_max_good (Generic.sample stream t)

/-- The presentation starting with 1 and then interleaving 3, 2, 5, 4, and so on. -/
def badStream (n : ℕ) : ℕ := if n = 0 then 1 else if n % 2 = 1 then n + 2 else n

theorem badStream_presents : Generic.Presents badStream language := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    change 0 < badStream n
    unfold badStream
    split_ifs <;> omega
  · intro hx
    change 0 < x at hx
    by_cases h1 : x = 1
    · exact ⟨0, by simp [badStream, h1]⟩
    · by_cases ho : x % 2 = 1
      · refine ⟨x - 2, ?_⟩
        have hn : x - 2 ≠ 0 := by omega
        have hodd : (x - 2) % 2 = 1 := by omega
        simp only [badStream, ite_eq_right hn, ite_eq_left hodd]
        omega
      · exact ⟨x, by simp [badStream, show x ≠ 0 by omega, ho]⟩

theorem bad_sample_gap {k : ℕ} (_ : 1 ≤ k) : 2 * k ∉ Generic.sample badStream (2 * k) := by
  intro h
  obtain ⟨n, hn, he⟩ := Generic.mem_sample_iff.mp h
  unfold badStream at he
  split_ifs at he <;> omega

theorem bad_sample_large {k : ℕ} (hk : 1 ≤ k) :
    2 * k + 1 ∈ Generic.sample badStream (2 * k) := by
  apply Generic.mem_sample_iff.mpr
  refine ⟨2 * k - 1, by omega, ?_⟩
  have hn : 2 * k - 1 ≠ 0 := by omega
  have ho : (2 * k - 1) % 2 = 1 := by omega
  simp only [badStream, ite_eq_right hn, ite_eq_left ho]
  omega

/-- Evaluate the counterexample output after sorting the observed sample. -/
def sortedOutput (S : Finset ℕ) : ℕ := output (S.sort (· ≤ ·))

theorem sorted_output_zero {k : ℕ} (hk : 1 ≤ k) :
    sortedOutput (Generic.sample badStream (2 * k)) = 0 := by
  classical
  let S := Generic.sample badStream (2 * k)
  have hne : S ≠ Finset.Icc 1 (S.sup id) := by
    intro he
    have hsup : 2 * k + 1 ≤ S.sup id := Finset.le_sup (f := id) (bad_sample_large hk)
    have hh : 2 * k ∈ Finset.Icc 1 (S.sup id) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [← he] at hh
    exact bad_sample_gap hk hh
  change output (S.sort (· ≤ ·)) = 0
  rw [output, ite_eq_left ?_]
  exact ⟨S.sortedLT_sort.pairwise, by simpa only [Finset.sort_toFinset] using hne⟩

theorem sorted_generator_fails : ¬ Generic.IsLimitGenerator (ofSet sortedOutput) {language} := by
  intro h
  obtain ⟨N, hN⟩ := h language rfl badStream badStream_presents
  have hg := (hN (2 * (N + 1)) (by omega)).1
  rw [output_ofSet, sorted_output_zero (by omega : 1 ≤ N + 1)] at hg
  exact Nat.lt_irrefl 0 hg

theorem sorting_counterexample :
    Generic.IsLimitGenerator generator {language} ∧
      ¬ Generic.IsLimitGenerator (ofSet sortedOutput) {language} :=
  ⟨generator_success, sorted_generator_fails⟩

end GenLimit.FiniteWitness.Sorting
