/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import Mathlib.Order.KonigLemma
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic

/-!
# The finite-color interval lemma used for termination

The operation colors in the proof of the Flag Decomposition Lemma need not
decrease.  The combinatorial input instead finds an interval with many
occurrences of its least color.  The required number of occurrences may
depend arbitrarily on the first index of the interval.
-/

namespace EGZ

open scoped BigOperators

/-- An interval on which `l` is a lower bound for the colors and occurs at
least `h a` times.  Indices and colors start at zero. -/
def HasColorInterval (χ : ℕ → ℕ) (h : ℕ → ℕ) (a b l : ℕ) : Prop :=
  a ≤ b ∧ (∀ i ∈ Finset.Icc a b, l ≤ χ i) ∧
    h a ≤ ((Finset.Icc a b).filter fun i => χ i = l).card

theorem HasColorInterval.congr {χ ψ : ℕ → ℕ} {h : ℕ → ℕ} {a b l : ℕ}
    (hχ : HasColorInterval χ h a b l)
    (heq : ∀ i ∈ Finset.Icc a b, χ i = ψ i) :
    HasColorInterval ψ h a b l := by
  rcases hχ with ⟨hab, hlow, hcard⟩
  refine ⟨hab, fun i hi => by rw [← heq i hi]; exact hlow i hi, ?_⟩
  convert hcard using 1
  congr 1
  exact Finset.filter_congr fun i hi => by rw [heq i hi]

/-- Infinite version of the interval lemma: take the least color whose
fiber is infinite, then start beyond every occurrence of a smaller color. -/
theorem exists_color_interval (k : ℕ) (h χ : ℕ → ℕ) (hχ : ∀ i, χ i < k) :
    ∃ a b l, l < k ∧ HasColorInterval χ h a b l := by
  classical
  have hinf : ∃ l, l < k ∧ Set.Infinite {i | χ i = l} := by
    obtain ⟨l, hl⟩ := Finite.exists_infinite_fiber (fun i => (⟨χ i, hχ i⟩ : Fin k))
    refine ⟨l, l.isLt, ?_⟩
    have hh := Set.infinite_coe_iff.mp hl
    simpa only [Set.preimage, Set.mem_singleton_iff, Fin.ext_iff] using hh
  let l := Nat.find hinf
  have hl : l < k ∧ Set.Infinite {i | χ i = l} := Nat.find_spec hinf
  have hsmall : ∀ c < l, Set.Finite {i | χ i = c} := by
    intro c hc
    by_contra hcfin
    exact Nat.find_min hinf hc ⟨hc.trans hl.1, hcfin⟩
  have hbad : Set.Finite {i | χ i < l} := by
    apply ((Finset.range l).finite_toSet.biUnion fun c hc =>
      hsmall c (Finset.mem_range.mp hc)).subset
    intro i hi
    exact Set.mem_iUnion₂.mpr ⟨χ i, Finset.mem_range.mpr hi, rfl⟩
  obtain ⟨a₀, ha₀⟩ := hbad.bddAbove
  let a := a₀ + 1
  have hlow : ∀ i, a ≤ i → l ≤ χ i := by
    intro i hi
    by_contra hli
    have hia := ha₀ (show i ∈ {i | χ i < l} from Nat.lt_of_not_ge hli)
    omega
  have htail : Set.Infinite ({i | χ i = l} \ Set.Iio a) :=
    hl.2.sdiff (Set.finite_Iio a)
  obtain ⟨s, hs, hcard⟩ := htail.exists_subset_card_eq (h a)
  let b := max a (s.sup id)
  refine ⟨a, b, l, hl.1, le_max_left _ _, ?_, ?_⟩
  · intro i hi
    exact hlow i (Finset.mem_Icc.mp hi).1
  · rw [← hcard]
    apply Finset.card_le_card
    intro i hi
    have his := hs hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, his.1⟩
    · exact Nat.le_of_not_gt his.2
    · exact (Finset.le_sup (f := id) hi).trans (le_max_right _ _)

/-- Extend a coloring of a finite initial segment by zero.  Only values in
the original segment will occur in the conclusions below. -/
def extendColoring {n k : ℕ} (χ : Fin n → Fin k) (i : ℕ) : ℕ :=
  if hi : i < n then (χ ⟨i, hi⟩).val else 0

private def BadColoring (k : ℕ) (h : ℕ → ℕ) (n : ℕ) :=
  {χ : Fin n → Fin k // ¬ ∃ a b l, b < n ∧
    HasColorInterval (extendColoring χ) h a b l}

private def restrictBadColoring {k : ℕ} {h : ℕ → ℕ} {n m : ℕ}
    (hnm : n ≤ m) (χ : BadColoring k h m) : BadColoring k h n := by
  refine ⟨fun i => χ.val (Fin.castLE hnm i), ?_⟩
  rintro ⟨a, b, l, hbn, hab⟩
  apply χ.property
  refine ⟨a, b, l, hbn.trans_le hnm, hab.congr ?_⟩
  intro i hi
  have hin : i < n := (Finset.mem_Icc.mp hi).2.trans_lt hbn
  have him : i < m := hin.trans_le hnm
  simp [extendColoring, hin, him]

/-- The finite-color interval claim in the proof of the Flag Decomposition
Lemma.  The bound is uniform over all colorings and `h` need not be
monotone.  Kőnig's lemma turns arbitrarily long bad colorings into an
infinite bad coloring, contradicting `exists_color_interval`. -/
theorem exists_finite_color_interval_bound (k : ℕ) (h : ℕ → ℕ) :
    ∃ N, ∀ χ : Fin N → Fin k, ∃ a b l,
      b < N ∧ HasColorInterval (extendColoring χ) h a b l := by
  classical
  by_contra hno
  push Not at hno
  have hnonempty (n : ℕ) : Nonempty (BadColoring k h n) := by
    obtain ⟨χ, hχ⟩ := hno n
    exact ⟨χ, by simpa only [not_exists, not_and] using hχ⟩
  have (n : ℕ) : Nonempty (BadColoring k h n) := hnonempty n
  have (n : ℕ) : Finite (BadColoring k h n) := by
    unfold BadColoring
    infer_instance
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite
    (α := BadColoring k h)
    (fun hnm χ => restrictBadColoring hnm χ)
    (by intro i χ; apply Subtype.ext; funext j; rfl)
    (by intro i j m hij hjm χ; apply Subtype.ext; funext t; rfl)
    (by intro i χ; exact Set.toFinite _)
  let χ : ℕ → ℕ := fun i => ((f (i + 1)).val ⟨i, Nat.lt_succ_self i⟩).val
  have hχ : ∀ i, χ i < k := fun i => ((f (i + 1)).val ⟨i, Nat.lt_succ_self i⟩).isLt
  obtain ⟨a, b, l, _, hab⟩ := exists_color_interval k h χ hχ
  apply (f (b + 1)).property
  refine ⟨a, b, l, Nat.lt_succ_self b, hab.congr ?_⟩
  intro i hi
  have hib : i ≤ b := (Finset.mem_Icc.mp hi).2
  have heq := congrArg
    (fun w : BadColoring k h (i + 1) => (w.val ⟨i, Nat.lt_succ_self i⟩).val)
    (hf (Nat.succ_le_succ hib))
  simpa [χ, restrictBadColoring, extendColoring, Nat.lt_succ_of_le hib] using heq.symm

/-- A formulation for operation sequences: among the first `N` operations,
there is an interval whose smallest color occurs as often as prescribed by
the interval's starting index.  Only these first `N` colors are constrained. -/
theorem exists_color_interval_bound (k : ℕ) (h : ℕ → ℕ) :
    ∃ N, ∀ χ : ℕ → ℕ, (∀ i < N, χ i < k) →
      ∃ a b l, b < N ∧ l < k ∧ HasColorInterval χ h a b l := by
  obtain ⟨N, hN⟩ := exists_finite_color_interval_bound k h
  refine ⟨N, ?_⟩
  intro χ hχ
  let χfin : Fin N → Fin k := fun i => ⟨χ i, hχ i i.isLt⟩
  obtain ⟨a, b, l, hbn, hab⟩ := hN χfin
  have hgood : HasColorInterval χ h a b l := hab.congr (by
    intro i hi
    have hin : i < N := (Finset.mem_Icc.mp hi).2.trans_lt hbn
    simp [extendColoring, hin, χfin])
  refine ⟨a, b, l, hbn, ?_, hgood⟩
  exact (hgood.2.1 a (Finset.mem_Icc.mpr ⟨le_rfl, hgood.1⟩)).trans_lt
    (hχ a (hgood.1.trans_lt hbn))

end EGZ
