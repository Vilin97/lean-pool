/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.Slaloms
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Encodable.Lattice
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic

/-!
# Coding a slalom cover into strong infinite coincidence

Finite graphs are coded by natural numbers. Candidate `j` at coordinate `n` is
read at stage `Nat.pair n j`; at each stage the decoder chooses a fresh argument.
A sufficiently large graph coded by a caught value therefore yields a fresh
correct coincidence, even on any prescribed infinite subset of the naturals.
-/

open Finset Filter Cardinal

noncomputable section

namespace NonMRR

private def graphDecode (a : ℕ) : Finset (ℕ × ℕ) :=
  (Encodable.decode (α := Finset (ℕ × ℕ)) a).getD ∅

private theorem graphDecode_encode (s : Finset (ℕ × ℕ)) :
    graphDecode (Encodable.encode s) = s := by
  simp [graphDecode]

private def freshPair (s : Finset (ℕ × ℕ)) (u : Finset ℕ) : ℕ × ℕ := by
  classical
  exact if h : ∃ p ∈ s, p.1 ∉ u then h.choose else (u.sup id + 1, 0)

private theorem freshPair_fresh (s : Finset (ℕ × ℕ)) (u : Finset ℕ) :
    (freshPair s u).1 ∉ u := by
  classical
  unfold freshPair
  split_ifs with h
  · exact h.choose_spec.2
  · intro hu
    have hh := le_sup (f := id) hu
    simp only [id_eq] at hh
    omega

private theorem freshPair_mem (s : Finset (ℕ × ℕ)) (u : Finset ℕ)
    (hcard : u.card < (s.image Prod.fst).card) : freshPair s u ∈ s := by
  classical
  have hex : ∃ p ∈ s, p.1 ∉ u := by
    by_contra h
    push Not at h
    have hsub : s.image Prod.fst ⊆ u := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
      exact h p hp
    exact (not_le_of_gt hcard) (card_le_card hsub)
  simp only [freshPair, dite_eq_left hex]
  exact hex.choose_spec.1

private def graphHistory (a : ℕ → ℕ) : ℕ → Finset (ℕ × ℕ)
  | 0 => ∅
  | n + 1 => insert (freshPair (graphDecode (a n)) ((graphHistory a n).image Prod.fst))
    (graphHistory a n)

private def graphChoice (a : ℕ → ℕ) (n : ℕ) : ℕ × ℕ :=
  freshPair (graphDecode (a n)) ((graphHistory a n).image Prod.fst)

private theorem graphHistory_card (a : ℕ → ℕ) (n : ℕ) : (graphHistory a n).card ≤ n := by
  induction n with
  | zero => simp [graphHistory]
  | succ n hn => exact (card_insert_le _ _).trans (Nat.add_le_add_right hn 1)

private theorem graphHistory_mono (a : ℕ → ℕ) : Monotone (graphHistory a) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_insert _ _

private theorem graphChoice_mem_history (a : ℕ → ℕ) (n : ℕ) :
    graphChoice a n ∈ graphHistory a (n + 1) := mem_insert_self _ _

private theorem graphChoice_fresh (a : ℕ → ℕ) (n : ℕ) :
    (graphChoice a n).1 ∉ (graphHistory a n).image Prod.fst :=
  freshPair_fresh _ _

private theorem graphChoice_injective (a : ℕ → ℕ) :
    Function.Injective (fun n => (graphChoice a n).1) := by
  intro n m hnm
  dsimp only at hnm
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hm := graphChoice_fresh a m
    apply hm
    rw [← hnm]
    exact mem_image_of_mem _ ((graphHistory_mono a (by omega)) (graphChoice_mem_history a n))
  · have hn := graphChoice_fresh a n
    apply hn
    rw [hnm]
    exact mem_image_of_mem _ ((graphHistory_mono a (by omega)) (graphChoice_mem_history a m))

private def graphResponse (a : ℕ → ℕ) : ℕ → ℕ :=
  Function.extend (fun n => (graphChoice a n).1) (fun n => (graphChoice a n).2) 0

private theorem graphResponse_choice (a : ℕ → ℕ) (n : ℕ) :
    graphResponse a (graphChoice a n).1 = (graphChoice a n).2 := by
  exact (graphChoice_injective a).extend_apply _ _ n

private def candidateAt (s : Finset ℕ) (j : ℕ) : ℕ :=
  if hj : j < s.card then ((s.orderIsoOfFin rfl) ⟨j, hj⟩).val else 0

private theorem candidateAt_covers (s : Finset ℕ) {a : ℕ} (ha : a ∈ s) :
    ∃ j < s.card, candidateAt s j = a := by
  let e := s.orderIsoOfFin rfl
  let i := e.symm ⟨a, ha⟩
  refine ⟨i.val, i.isLt, ?_⟩
  simp only [candidateAt, dite_eq_left i.isLt]
  exact congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)

private def slalomStages (φ : ℕ → Finset ℕ) (x : ℕ) : ℕ :=
  candidateAt (φ (Nat.unpair x).1) (Nat.unpair x).2

private theorem slalomStages_pair (φ : ℕ → Finset ℕ) (n j : ℕ) :
    slalomStages φ (Nat.pair n j) = candidateAt (φ n) j := by
  simp [slalomStages]

/-- The coincidence response associated with a finite-set-valued slalom. -/
def slalomCoincidenceResponse (φ : ℕ → Finset ℕ) : ℕ → ℕ :=
  graphResponse (slalomStages φ)

private def graphSize (r : ℕ → ℕ) (n : ℕ) : ℕ :=
  (range (r n)).sup (Nat.pair n) + 1

private theorem pair_lt_graphSize (r : ℕ → ℕ) {n j : ℕ} (hj : j < r n) :
    Nat.pair n j < graphSize r n := by
  have h := le_sup (f := Nat.pair n) (mem_range.2 hj)
  exact Nat.lt_succ_of_le h

private def finiteGraph (w : ℕ ↪ ℕ) (c : ℕ → ℕ) (N : ℕ) : Finset (ℕ × ℕ) :=
  (range N).image (fun i => (w i, c (w i)))

private theorem finiteGraph_domain_card (w : ℕ ↪ ℕ) (c : ℕ → ℕ) (N : ℕ) :
    ((finiteGraph w c N).image Prod.fst).card = N := by
  simp only [finiteGraph, image_image, Function.comp_def]
  rw [card_image_of_injective _ w.injective, card_range]

private theorem graphChoice_of_correct_code (a : ℕ → ℕ) (w : ℕ ↪ ℕ)
    (c : ℕ → ℕ) {x N : ℕ} (hx : x < N)
    (hcode : a x = Encodable.encode (finiteGraph w c N)) :
    ∃ i < N, graphChoice a x = (w i, c (w i)) := by
  have hdecode : graphDecode (a x) = finiteGraph w c N := by
    rw [hcode, graphDecode_encode]
  have hcard : ((graphHistory a x).image Prod.fst).card <
      ((graphDecode (a x)).image Prod.fst).card := by
    rw [hdecode, finiteGraph_domain_card]
    exact (card_image_le.trans (graphHistory_card a x)).trans_lt hx
  have hmem := freshPair_mem (graphDecode (a x)) ((graphHistory a x).image Prod.fst) hcard
  rw [hdecode] at hmem
  obtain ⟨i, hi, hip⟩ := mem_image.1 hmem
  refine ⟨i, mem_range.1 hi, ?_⟩
  simpa only [graphChoice, hdecode] using hip.symm

/-- A dominating family of slaloms can be coded, without increasing its
cardinality, into a family that agrees infinitely often with every prescribed
function on every prescribed infinite set of coordinates. -/
theorem slalom_cover_to_strong_coincidence (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (Φ : Set (Slalom r)) (hΦ : (slalomRelation r hr).Dominating Φ) :
    ∃ F : Set (ℕ → ℕ), #F ≤ #Φ ∧
      ∀ W : Set ℕ, W.Infinite → ∀ c : ℕ → ℕ,
        ∃ f ∈ F, ∃ᶠ n in atTop, n ∈ W ∧ f n = c n := by
  classical
  refine ⟨(fun φ : Slalom r => slalomCoincidenceResponse φ.val) '' Φ,
    Cardinal.mk_image_le, ?_⟩
  intro W hW c
  let w : ℕ ↪ ℕ := (hW.natEmbedding W).trans (Function.Embedding.subtype W)
  have hw (i : ℕ) : w i ∈ W := (hW.natEmbedding W i).property
  let e : ℕ → ℕ := fun n => Encodable.encode (finiteGraph w c (graphSize r n))
  obtain ⟨φ, hφ, hcatch⟩ := hΦ e
  refine ⟨slalomCoincidenceResponse φ.val, Set.mem_image_of_mem _ hφ, ?_⟩
  have hc : ∃ᶠ n in atTop, e n ∈ φ.val n := hcatch
  rw [frequently_atTop] at hc ⊢
  intro M
  have ht := (graphChoice_injective (slalomStages φ.val)).nat_tendsto_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_atTop.1 ht) M)
  obtain ⟨n, hn, hcn⟩ := hc K
  obtain ⟨j, hj, hej⟩ := candidateAt_covers (φ.val n) hcn
  have hjr : j < r n := hj.trans_le (φ.property n)
  have hcode : slalomStages φ.val (Nat.pair n j) =
      Encodable.encode (finiteGraph w c (graphSize r n)) := by
    rw [slalomStages_pair, hej]
  obtain ⟨i, _hi, hchoice⟩ := graphChoice_of_correct_code
    (slalomStages φ.val) w c (pair_lt_graphSize r hjr) hcode
  have hM := hK (Nat.pair n j) (hn.trans (Nat.left_le_pair n j))
  refine ⟨w i, ?_, hw i, ?_⟩
  · simpa only [hchoice] using hM
  · change graphResponse (slalomStages φ.val) (w i) = c (w i)
    simpa only [hchoice] using graphResponse_choice (slalomStages φ.val) (Nat.pair n j)

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
