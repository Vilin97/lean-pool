/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.CategoryBlocks

/-!
# From coincidence families to a nonmeagre set

The finite-block description is combined with the explicit pasting of
separated blocks. All cardinal estimates use images of actual families.
-/

open Set Filter Cardinal

namespace NonMRR

/-- A family meeting each prescribed function infinitely often along
each infinite set of coordinates. -/
def StronglyCoincident (F : Set (ℕ → ℕ)) : Prop :=
  ∀ W : Set ℕ, W.Infinite → ∀ c : ℕ → ℕ,
    ∃ f ∈ F, ∃ᶠ n in atTop, n ∈ W ∧ f n = c n

/-- A family of increasing sequences with gaps escaping each bound. -/
def GapUnbounded (B : Set (ℕ → ℕ)) : Prop :=
  (∀ t ∈ B, StrictMono t) ∧ ∀ g : ℕ → ℕ,
    ∃ t ∈ B, ∃ᶠ k in atTop, g (t k) < t (k + 1)

/-- Finite binary words, including the empty word. -/
abbrev FiniteBinaryWord := Σ m : ℕ, Fin m → Bool

/-- The endpoint of a word placed at coordinate `n`. -/
def wordEnd (n : ℕ) (w : FiniteBinaryWord) : ℕ := n + w.1

/-- Read a word at offset `i - n`, returning `false` past its endpoint. -/
def wordValue (n : ℕ) (w : FiniteBinaryWord) (i : ℕ) : Bool :=
  if hi : i - n < w.1 then w.2 ⟨i - n, hi⟩ else false

/-- Encode a finite restriction of a binary sequence as a word. -/
def restrictWord (n m : ℕ) (a : ℕ → Bool) : FiniteBinaryWord :=
  ⟨m - n, fun i => a (n + i)⟩

theorem wordEnd_restrictWord {n m : ℕ} (hnm : n ≤ m) (a : ℕ → Bool) :
    wordEnd n (restrictWord n m a) = m := by
  simp only [wordEnd, restrictWord]
  omega

theorem wordValue_restrictWord {n m i : ℕ} (hni : n ≤ i) (him : i < m)
    (a : ℕ → Bool) : wordValue n (restrictWord n m a) i = a i := by
  have hlen : i - n < m - n := by omega
  simp [wordValue, restrictWord, hlen, Nat.add_sub_of_le hni]

/-- The central category reduction: pasting a gap-unbounded family and
a strong coincidence family yields a nonmeagre set of the expected size. -/
theorem exists_nonmeagre_of_gap_and_coincidence
    {B F : Set (ℕ → ℕ)} (hB : GapUnbounded B) (hF : StronglyCoincident F) :
    ∃ Y : Set (ℕ → Bool), ¬ IsMeagre Y ∧
      Cardinal.mk Y ≤ Cardinal.mk B * Cardinal.mk F := by
  classical
  obtain ⟨decode, hdecode⟩ := exists_surjective_nat FiniteBinaryWord
  let endOf (f : ℕ → ℕ) (n : ℕ) := wordEnd n (decode (f n))
  let bitsOf (f : ℕ → ℕ) (n i : ℕ) := wordValue n (decode (f n)) i
  choose paste hpaste using fun (t : B) (f : F) =>
    exists_pasted_blocks t (hB.1 t t.2) (endOf f) (bitsOf f)
  let Y : Set (ℕ → Bool) := Set.range (fun p : B × F => paste p.1 p.2)
  refine ⟨Y, ?_, ?_⟩
  · intro hY
    obtain ⟨g, a, hg, hcover⟩ := meagre_subset_eventually_misses_blocks hY
    choose c hc using fun n => hdecode (restrictWord n (g n) (a n))
    obtain ⟨t, htB, htgap⟩ := hB.2 g
    have ht : StrictMono t := hB.1 t htB
    let W : Set ℕ := t '' {k | g (t k) < t (k + 1)}
    have hWinf : W.Infinite :=
      (Nat.frequently_atTop_iff_infinite.mp htgap).image ht.injective.injOn
    obtain ⟨f, hfF, hfreq⟩ := hF W hWinf c
    let x : ℕ → Bool := paste ⟨t, htB⟩ ⟨f, hfF⟩
    have hxY : x ∈ Y := ⟨(⟨t, htB⟩, ⟨f, hfF⟩), rfl⟩
    have hmiss := hcover x hxY
    obtain ⟨n, ⟨hnW, hnc⟩, hnmiss⟩ := (hfreq.and_eventually hmiss).exists
    obtain ⟨k, hkgap, hkn⟩ := hnW
    subst n
    have hword : decode (f (t k)) = restrictWord (t k) (g (t k)) (a (t k)) := by
      rw [hnc]
      exact hc (t k)
    have hend : endOf f (t k) = g (t k) := by
      simp only [endOf, hword]
      exact wordEnd_restrictWord (hg (t k)).le _
    apply hnmiss
    intro i hki hig
    have hp := hpaste ⟨t, htB⟩ ⟨f, hfF⟩ k
      (show endOf f (t k) < t (k + 1) by rwa [hend]) i hki
      (show i < endOf f (t k) by rwa [hend])
    change x i = bitsOf f (t k) i at hp
    rw [hp]
    change wordValue (t k) (decode (f (t k))) i = a (t k) i
    rw [hword]
    exact wordValue_restrictWord hki hig _
  · have hcard : Cardinal.mk Y ≤ Cardinal.mk (B × F) := Cardinal.mk_range_le
    simpa only [Cardinal.mk_prod, Cardinal.lift_id] using hcard

theorem nonMeagreCardinal_le_product_of_gap_and_coincidence
    {B F : Set (ℕ → ℕ)} (hB : GapUnbounded B) (hF : StronglyCoincident F) :
    nonMeagreCardinal (ℕ → Bool) ≤ Cardinal.mk B * Cardinal.mk F := by
  obtain ⟨Y, hY, hcard⟩ := exists_nonmeagre_of_gap_and_coincidence hB hF
  exact (nonMeagreCardinal_le_mk hY).trans hcard

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
