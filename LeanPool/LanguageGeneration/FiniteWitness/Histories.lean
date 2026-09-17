/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
import LeanPool.LanguageGeneration.FiniteWitness.Basic
import LeanPool.LanguageGeneration.Core.Text
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Infix

/-! # Exhaustive limits of nested finite histories -/

namespace GenLimit.FiniteWitness

open GenLimit.Generic

variable {α : Type*}

@[simp] theorem prefix_toFinset [DecidableEq α] (stream : Stream α) (t : ℕ) :
    (GenLimit.textPrefix stream t).toFinset = Generic.sample stream t := by
  classical
  ext x
  simp [GenLimit.textPrefix, Generic.sample]

/-- Evaluate an ordered-history generator on a finite list of observations. -/
def listOutput (G : Generator α) (xs : List α) : α := G xs.length xs.get

@[simp] theorem listOutput_prefix (G : Generator α) (stream : Stream α) (t : ℕ) :
    listOutput G (GenLimit.textPrefix stream t) = output G stream t := by
  unfold listOutput output
  congr 1
  · simp
  · apply (Fin.heq_fun_iff (GenLimit.textPrefix_length stream t)).mpr
    intro i
    change (List.map stream (List.range t))[i.val] = stream i.val
    simp

/-- Eventual target validity of a list-input function; freshness is separate. -/
def EventuallyValid (F : List α → α) (L : Generic.Language α) : Prop :=
  ∀ stream : Stream α, Generic.Presents stream L →
    ∃ t₀, ∀ t, t₀ ≤ t → F (GenLimit.textPrefix stream t) ∈ L

/-- A list-input function always returns an element absent from its input. -/
def Fresh (F : List α → α) : Prop := ∀ xs, F xs ∉ xs

/-- Replace a previously observed output by a fresh element of the infinite universe. -/
noncomputable def freshRepair [Infinite α] (G : Generator α) (xs : List α) : α := by
  classical
  exact if listOutput G xs ∈ xs then xs.toFinset.exists_notMem.choose
    else listOutput G xs

theorem freshRepair_fresh [Infinite α] (G : Generator α) : Fresh (freshRepair G) := by
  classical
  intro xs
  by_cases h : listOutput G xs ∈ xs
  · simpa [freshRepair, h] using xs.toFinset.exists_notMem.choose_spec
  · simp [freshRepair, h]

theorem freshRepair_eventuallyValid [Infinite α] {G : Generator α}
    {H : LanguageClass α} (hG : IsLimitGenerator G H) {L : Generic.Language α}
    (hL : L ∈ H) : EventuallyValid (freshRepair G) L := by
  classical
  intro stream hP
  obtain ⟨t₀, ht₀⟩ := hG L hL stream hP
  refine ⟨t₀, ?_⟩
  intro t ht
  have hgood := ht₀ t ht
  have hfresh : listOutput G (GenLimit.textPrefix stream t) ∉
      GenLimit.textPrefix stream t := by
    simpa [← List.mem_toFinset, CorrectAt] using hgood.2
  rw [freshRepair, ite_eq_right hfresh]
  simpa only [listOutput_prefix] using hgood.1

theorem history_prefix_mono {v : ℕ → List α}
    (hp : ∀ n, v n <+: v (n + 1)) {n m : ℕ} (hnm : n ≤ m) : v n <+: v m := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih => exact ih.trans (hp m)

/-- The stream determined by a nested sequence whose lengths tend to infinity. -/
def chainStream (v : ℕ → List α) (hlen : ∀ n, n ≤ (v n).length) : Stream α :=
  fun k => (v (k + 1)).get ⟨k, by have := hlen (k + 1); omega⟩

theorem chainStream_eq_get {v : ℕ → List α}
    (hp : ∀ n, v n <+: v (n + 1)) (hlen : ∀ n, n ≤ (v n).length)
    (n k : ℕ) (hk : k < (v n).length) :
    chainStream v hlen k = (v n).get ⟨k, hk⟩ := by
  rw [chainStream, List.get_eq_getElem, List.get_eq_getElem]
  have hb : k < (v (k + 1)).length := by have := hlen (k + 1); omega
  rcases le_total (k + 1) n with h | h
  · exact (List.prefix_iff_getElem.mp (history_prefix_mono hp h)).2 k hb
  · exact ((List.prefix_iff_getElem.mp (history_prefix_mono hp h)).2 k hk).symm

theorem prefix_chainStream {v : ℕ → List α}
    (hp : ∀ n, v n <+: v (n + 1)) (hlen : ∀ n, n ≤ (v n).length) (n : ℕ) :
    GenLimit.textPrefix (chainStream v hlen) (v n).length = v n := by
  apply List.ext_get
  · simp [GenLimit.textPrefix]
  · intro k hk₁ hk₂
    simp only [GenLimit.textPrefix, List.get_eq_getElem, List.getElem_map,
      List.getElem_range]
    exact chainStream_eq_get hp hlen n k hk₂

theorem chainStream_presents {v : ℕ → List α} {L : Generic.Language α}
    (hp : ∀ n, v n <+: v (n + 1)) (hlen : ∀ n, n ≤ (v n).length)
    (hlegal : ∀ n, ∀ x ∈ v n, x ∈ L)
    (hexhaust : ∀ x ∈ L, ∃ n, x ∈ v n) :
    Generic.Presents (chainStream v hlen) L := by
  apply Set.Subset.antisymm
  · rintro x ⟨k, rfl⟩
    exact hlegal (k + 1) _ (List.get_mem _ _)
  · intro x hx
    obtain ⟨n, hn⟩ := hexhaust x hx
    rw [← prefix_chainStream hp hlen n] at hn
    obtain ⟨k, _, hk⟩ := GenLimit.mem_textPrefix_iff.mp hn
    exact ⟨k, hk⟩

/-- An exhaustive chain cannot have bad outputs at every positive stage. -/
theorem no_exhaustive_bad_chain {F : List α → α} {L : Generic.Language α}
    (hvalid : EventuallyValid F L) (v : ℕ → List α)
    (hp : ∀ n, v n <+: v (n + 1)) (hlen : ∀ n, n ≤ (v n).length)
    (hlegal : ∀ n, ∀ x ∈ v n, x ∈ L)
    (hexhaust : ∀ x ∈ L, ∃ n, x ∈ v n)
    (hbad : ∀ n, F (v (n + 1)) ∉ L) : False := by
  obtain ⟨t₀, ht₀⟩ := hvalid (chainStream v hlen)
    (chainStream_presents hp hlen hlegal hexhaust)
  have hlen₀ : t₀ ≤ (v (t₀ + 1)).length := (Nat.le_succ t₀).trans (hlen _)
  have hgood := ht₀ (v (t₀ + 1)).length hlen₀
  rw [prefix_chainStream hp hlen] at hgood
  exact hbad t₀ hgood

end GenLimit.FiniteWitness
