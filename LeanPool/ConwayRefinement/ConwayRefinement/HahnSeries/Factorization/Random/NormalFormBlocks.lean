/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.NonPrincipalIrreducible
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NormalForm

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SeparatedSupport
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AdditivelyPrincipal
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Topology.Order.Monotone

/-!
# The block decomposition of a series of order type `ω^n · m + β`

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Theorem 1.8, treat a series `b` with `sup(b) = 0` and `ot(b) = m ω^α + β`, `β < ω^α`, through
its normal form (LM24, Definition 3.3.6 and Proposition 3.3.7, recalled as Definition 2.1):
`b = ∑ᵢ bᵢ t^{γᵢ} + r` with `b₁, …, bₘ ∈ P_α`, `γ₁ < ⋯ < γₘ ≤ 0` and `deg(r) < α`. The source
does not spell out this reading of the normal form; it is carried out here for `α = n < ω`.

The normal form lists principal terms `bᵢ t^{γᵢ}` with supports in strictly increasing
position and order types forming the Cantor normal form of `ot(b)`. When
`ot(b) = ω^n · m + β` with `β < ω^n`, the first `m` terms have order type `ω^n` and the remaining
ones order types below `ω^n`; the latter sum to `r`. The exponents of the first `m` terms are
strictly increasing: two consecutive terms of order type `ω^n ≥ ω` cannot share their support
supremum, since the upper one would then be a single monomial.

The decomposition records, besides the identity `b = ∑ᵢ bᵢ t^{γᵢ} + r`, the position of the
supports: the support of each block `bᵢ t^{γᵢ}` lies strictly below that of the later blocks and
of `r`. These are the facts used to transfer randomness from `b` to `b₁, …, bₘ`.
-/

open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci HahnSeries HahnSeries.Nonpositive

variable {K : Type v} [Field K]

/-- The block decomposition `b = ∑ᵢ bᵢ t^{γᵢ} + r` of a series of order type `ω^n · m + β`,
`β < ω^n`: `m` principal blocks of degree `n` at strictly increasing exponents `γᵢ ≤ 0`, a rest
of degree below `n`, and the supports of the blocks lying in increasing position below the
support of the rest. -/
structure BlockDecomposition (b : Series K) (n m : ℕ) where
  /-- The principal blocks `b₁, …, bₘ`. -/
  block : Fin m → Series K
  /-- The exponents `γ₁ < ⋯ < γₘ`. -/
  exponent : Fin m → ℝ
  /-- The rest `r`. -/
  rest : Series K
  /-- Each block is principal. -/
  block_isPrincipal : ∀ i, IsPrincipal (block i)
  /-- Each block has degree `n`. -/
  block_degree : ∀ i, ((block i : Series K) : K⟦ℝ⟧).degree = ((n : NatOrdinal) : WithBot NatOrdinal)
  /-- The exponents are nonpositive. -/
  exponent_nonpos : ∀ i, exponent i ≤ 0
  /-- The exponents are strictly increasing. -/
  exponent_strictMono : StrictMono exponent
  /-- The rest has degree below `n`. -/
  rest_degree : (rest : K⟦ℝ⟧).degree < ((n : NatOrdinal) : WithBot NatOrdinal)
  /-- `b = ∑ᵢ bᵢ t^{γᵢ} + r`. -/
  eq_blockSum : b = blockSum block exponent exponent_nonpos rest
  /-- The support of an earlier block lies strictly below the support of a later block. -/
  piece_lt_piece : ∀ i j, i < j →
    ∀ x ∈ ((block i * single (exponent i) (1 : K) (exponent_nonpos i) : Series K) : K⟦ℝ⟧).support,
    ∀ y ∈ ((block j * single (exponent j) (1 : K) (exponent_nonpos j) : Series K) : K⟦ℝ⟧).support,
      x < y
  /-- The support of every block lies strictly below the support of the rest. -/
  piece_lt_rest : ∀ i,
    ∀ x ∈ ((block i * single (exponent i) (1 : K) (exponent_nonpos i) : Series K) : K⟦ℝ⟧).support,
    ∀ y ∈ (rest : K⟦ℝ⟧).support, x < y

namespace BlockDecomposition

variable {b : Series K} {n m : ℕ} (d : BlockDecomposition b n m)

/-- The `i`-th block in position, `bᵢ t^{γᵢ}`. -/
def piece (i : Fin m) : Series K :=
  d.block i * single (d.exponent i) (1 : K) (d.exponent_nonpos i)

theorem piece_def (i : Fin m) :
    d.piece i = d.block i * single (d.exponent i) (1 : K) (d.exponent_nonpos i) :=
  (rfl)

theorem coe_piece (i : Fin m) :
    ((d.piece i : Series K) : K⟦ℝ⟧) = translate (d.exponent i) (d.block i : K⟦ℝ⟧) := by
  rw [piece_def, Subring.coe_mul, coe_single, mul_single_one_eq_translate]

theorem eq_sum_piece_add_rest : b = ∑ i, d.piece i + d.rest :=
  d.eq_blockSum.trans (blockSum_def _ _ _ _)

/-- The support of an earlier piece lies strictly below the support of a later piece. -/
theorem piece_support_lt {i j : Fin m} (hij : i < j) {x y : ℝ}
    (hx : x ∈ ((d.piece i : Series K) : K⟦ℝ⟧).support)
    (hy : y ∈ ((d.piece j : Series K) : K⟦ℝ⟧).support) : x < y :=
  d.piece_lt_piece i j hij x hx y hy

/-- The support of every piece lies strictly below the support of the rest. -/
theorem piece_support_lt_rest (i : Fin m) {x y : ℝ}
    (hx : x ∈ ((d.piece i : Series K) : K⟦ℝ⟧).support) (hy : y ∈ (d.rest : K⟦ℝ⟧).support) :
    x < y :=
  d.piece_lt_rest i x hx y hy

end BlockDecomposition

/-- Every element of a list of ordinals is at most the ordinary sum of the list. -/
private theorem le_list_sum_of_mem {l : List Ordinal} {a : Ordinal} (ha : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons c l ih =>
      rw [List.sum_cons]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact le_self_add
      · exact (ih ha).trans le_add_self

/-- The Cantor terms of `ω^n · m + β` for `β < ω^n`: `m` copies of `ω^n` followed by the Cantor
terms of `β`. -/
theorem additivePrincipalTerms_omega0_opow_mul_add {n m : ℕ} {β : Ordinal}
    (hβ : β < Ordinal.omega0 ^ (n : Ordinal)) :
    (Ordinal.omega0 ^ (n : Ordinal) * m + β).additivePrincipalTerms =
      List.replicate m (Ordinal.omega0 ^ (n : Ordinal)) ++ β.additivePrincipalTerms := by
  symm
  apply Ordinal.additivePrincipalTerms_unique
  · rw [List.sum_append, List.sum_replicate, Ordinal.nsmul_eq_mul,
      Ordinal.additivePrincipalTerms_sum]
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rw [List.eq_of_mem_replicate ha]
      exact Ordinal.isAdditivelyPrincipal_omega0_opow _
    · exact Ordinal.isAdditivelyPrincipal_of_mem_additivePrincipalTerms ha
  · rw [List.sortedGE_iff_pairwise, List.pairwise_append]
    refine ⟨?_, List.sortedGE_iff_pairwise.mp (Ordinal.additivePrincipalTerms_sortedGE β),
      fun a ha c hc ↦ ?_⟩
    · rw [List.pairwise_iff_forall_sublist]
      intro a c hsub
      have ha := List.eq_of_mem_replicate (hsub.subset (List.mem_cons_self ..))
      have hc := List.eq_of_mem_replicate (hsub.subset (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      rw [ha, hc]
    · rw [List.eq_of_mem_replicate ha]
      exact ((le_list_sum_of_mem hc).trans_eq (Ordinal.additivePrincipalTerms_sum β)).trans hβ.le

/-- A Hahn series whose support has order type `ω^n` with `n ≥ 1` is not a monomial: its
support is not contained in a singleton. -/
private theorem not_subset_singleton_of_supportOrderType_eq {n : ℕ} (hn : 1 ≤ n) {x : K⟦ℝ⟧}
    (hx : x.supportOrderType = Ordinal.omega0 ^ (n : Ordinal)) (g : ℝ) :
    ¬ x.support ⊆ {g} := by
  intro hsub
  have hle : x.supportOrderType ≤ (HahnSeries.single g (1 : K)).supportOrderType :=
    supportOrderType_mono (by rw [HahnSeries.support_single_of_ne one_ne_zero]; exact hsub)
  rw [supportOrderType_single one_ne_zero, hx] at hle
  have hlt : (1 : Ordinal) < Ordinal.omega0 ^ (n : Ordinal) :=
    Ordinal.one_lt_omega0.trans_le (by
      calc Ordinal.omega0 = Ordinal.omega0 ^ (1 : Ordinal) := (Ordinal.opow_one _).symm
        _ ≤ Ordinal.omega0 ^ (n : Ordinal) :=
          Ordinal.opow_le_opow_right Ordinal.omega0_pos (by exact_mod_cast hn))
  exact absurd hle (not_le.mpr hlt)

/-- LM24, Proposition 3.3.7, read at order type `ω^n · m + β` with `β < ω^n` and `n ≥ 1`: the
normal form of `b` is a block decomposition with `m` blocks of degree `n`. -/
theorem exists_blockDecomposition {b : Series K} {n m : ℕ} (hn : 1 ≤ n) {β : Ordinal}
    (hβ : β < Ordinal.omega0 ^ (n : Ordinal))
    (hot : (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (n : Ordinal) * m + β) :
    Nonempty (BlockDecomposition b n m) := by
  classical
  obtain ⟨terms, hterms⟩ := exists_isNormalForm b
  obtain ⟨hsum, -, hprinc, -, hpair⟩ := isNormalForm_iff.mp hterms
  set L : List K⟦ℝ⟧ := terms.map NormalForm.Term.series with hL
  have htypes : L.map supportOrderType =
      List.replicate m (Ordinal.omega0 ^ (n : Ordinal)) ++ β.additivePrincipalTerms := by
    rw [hterms.isWeakNormalForm.supportOrderTypes_eq_additivePrincipalTerms, hot,
      additivePrincipalTerms_omega0_opow_mul_add hβ]
  have hlen : m ≤ L.length := by
    have := congrArg List.length htypes
    rw [List.length_map, List.length_append, List.length_replicate] at this
    omega
  have hlenT : m ≤ terms.length := by rwa [hL, List.length_map] at hlen
  -- The first `m` series have order type `ω^n`; the remaining ones have smaller order type.
  have htake : (L.take m).map supportOrderType =
      List.replicate m (Ordinal.omega0 ^ (n : Ordinal)) := by
    rw [List.map_take, htypes, List.take_left' (List.length_replicate ..)]
  have hdrop : (L.drop m).map supportOrderType = β.additivePrincipalTerms := by
    rw [List.map_drop, htypes, List.drop_left' (List.length_replicate ..)]
  have hot_take : ∀ y ∈ L.take m, y.supportOrderType = Ordinal.omega0 ^ (n : Ordinal) :=
    fun y hy ↦ List.eq_of_mem_replicate (htake ▸ List.mem_map_of_mem hy)
  have hot_drop : ∀ y ∈ L.drop m, y.supportOrderType < Ordinal.omega0 ^ (n : Ordinal) := by
    intro y hy
    have hmem : y.supportOrderType ∈ β.additivePrincipalTerms := hdrop ▸ List.mem_map_of_mem hy
    exact ((le_list_sum_of_mem hmem).trans_eq (Ordinal.additivePrincipalTerms_sum β)).trans_lt hβ
  -- The terms of the first `m` blocks.
  have hltT : ∀ i : Fin m, i.1 < terms.length := fun i ↦ lt_of_lt_of_le i.2 hlenT
  have hltL : ∀ i : Fin m, i.1 < L.length := fun i ↦ lt_of_lt_of_le i.2 hlen
  let tm : Fin m → NormalForm.Term K := fun i ↦ terms[i.1]'(hltT i)
  have htm_mem : ∀ i, tm i ∈ terms := fun i ↦ List.getElem_mem _
  have hLget : ∀ i : Fin m, L[i.1]'(hltL i) = (tm i).series := fun i ↦ by
    simp only [hL, List.getElem_map, tm]
  have hseries_mem : ∀ i, (tm i).series ∈ L.take m := by
    intro i
    rw [← hLget i,
      ← List.getElem_take (h := (by rw [List.length_take]; exact lt_min i.2 (hltL i)))]
    exact List.getElem_mem _
  have hprinc' : ∀ i, IsPrincipal (tm i).coefficient := fun i ↦ hprinc _ (htm_mem i)
  have hot_tm : ∀ i, ((tm i).coefficient : K⟦ℝ⟧).supportOrderType =
      Ordinal.omega0 ^ (n : Ordinal) := fun i ↦ by
    rw [← supportOrderType_translate (tm i).exponent, ← NormalForm.Term.series_eq_translate]
    exact hot_take _ (hseries_mem i)
  have hexp : ∀ i, (tm i).exponent = sSup (tm i).series.support := fun i ↦
    (NormalForm.Term.csSup_support_series (tm i) (hprinc' i)).symm
  have hseries_ne : ∀ i, (tm i).series ≠ 0 := fun i ↦
    NormalForm.Term.series_ne_zero (hprinc' i)
  have hsub_b : ∀ i, (tm i).series.support ⊆ (b : K⟦ℝ⟧).support := fun i ↦ by
    rw [← hsum]
    exact support_subset_list_sum_of_mem hpair (List.mem_map_of_mem (htm_mem i))
  -- Pairwise position of the series.
  have hlenL : (L.take m).length = m := by
    rw [List.length_take]; exact min_eq_left hlen
  have hbelow : ∀ i j, i < j → SupportBelow (tm i).series (tm j).series := by
    intro i j hij
    rw [← hLget i, ← hLget j]
    have h := List.pairwise_iff_get.mp hpair ⟨i.1, hltL i⟩ ⟨j.1, hltL j⟩ (by simpa using hij)
    simpa only [List.get_eq_getElem] using h
  have hpairAll : (L.take m ++ L.drop m).Pairwise SupportBelow := by
    rw [List.take_append_drop]; exact hpair
  have hbelow_drop : ∀ i, SupportBelow (tm i).series (L.drop m).sum := by
    intro i
    apply supportBelow_list_sum
    intro y hy
    exact (List.pairwise_append.mp hpairAll).2.2 _ (hseries_mem i) y hy
  -- The exponents.
  have hexp_nonpos : ∀ i, (tm i).exponent ≤ 0 := fun i ↦ by
    rw [hexp i]
    exact csSup_le (support_nonempty_iff.mpr (hseries_ne i))
      fun x hx ↦ HahnSeries.Nonpositive.support_subset b (hsub_b i hx)
  have hexp_mono : StrictMono fun i ↦ (tm i).exponent := by
    intro i j hij
    have hbel := hbelow i j hij
    have hle : (tm i).exponent ≤ (tm j).exponent := by
      rw [hexp i, hexp j]
      exact csSup_support_le_of_supportBelow (hseries_ne i) (hseries_ne j)
        (NormalForm.Term.bddAbove_support _) hbel
    refine lt_of_le_of_ne hle fun heq ↦ ?_
    apply not_subset_singleton_of_supportOrderType_eq hn (hot_take _ (hseries_mem j))
      (tm j).exponent
    intro y hy
    have hy_le : y ≤ (tm j).exponent := by
      rw [hexp j]; exact le_csSup (NormalForm.Term.bddAbove_support _) hy
    have hy_ge : (tm i).exponent ≤ y := by
      rw [hexp i]
      exact csSup_le (support_nonempty_iff.mpr (hseries_ne i)) fun x hx ↦ (hbel.lt hx hy).le
    have heq' : (tm i).exponent = (tm j).exponent := heq
    exact Set.mem_singleton_iff.mpr (le_antisymm hy_le (heq' ▸ hy_ge))
  -- The sum of the first `m` series and the rest.
  have hsum_take : ∑ i, (tm i).series = (L.take m).sum := by
    have hofFn : List.ofFn (fun i : Fin m ↦ (tm i).series) = L.take m := by
      apply List.ext_getElem
      · rw [List.length_ofFn, hlenL]
      · intro i h₁ h₂
        have hi : i < m := by simpa using h₁
        rw [List.getElem_ofFn, ← hLget ⟨i, hi⟩, List.getElem_take]
    rw [← hofFn, List.sum_ofFn]
  have hsplit : L.sum = (L.take m).sum + (L.drop m).sum := by
    have h := List.sum_append (l₁ := L.take m) (l₂ := L.drop m)
    rwa [List.take_append_drop] at h
  have hrest : (b : K⟦ℝ⟧) - ∑ i, (tm i).series = (L.drop m).sum := by
    rw [hsum_take, ← hsum, hsplit]
    abel
  have hbelowSum : SupportBelow (L.take m).sum (L.drop m).sum := by
    apply list_sum_supportBelow
    intro x hx
    apply supportBelow_list_sum
    intro y hy
    exact (List.pairwise_append.mp hpairAll).2.2 x hx y hy
  have hdropsub : (L.drop m).sum.support ⊆ (b : K⟦ℝ⟧).support := by
    rw [← hsum, hsplit, support_add_eq_union_of_supportBelow _ _ hbelowSum]
    exact Set.subset_union_right
  have hrest_mem : (b : K⟦ℝ⟧) - ∑ i, (tm i).series ∈ nonpositiveSubring ℝ K := by
    rw [mem_nonpositiveSubring]
    intro y hy
    rw [hrest] at hy
    exact HahnSeries.Nonpositive.support_subset b (hdropsub hy)
  let rest : Series K := ⟨_, hrest_mem⟩
  have hcoe_rest : (rest : K⟦ℝ⟧) = (L.drop m).sum := hrest
  have hpairDrop : (L.drop m).Pairwise SupportBelow := hpair.sublist (List.drop_sublist m L)
  have hpiece : ∀ i, ((((tm i).coefficient * single (tm i).exponent (1 : K) (hexp_nonpos i)) :
      Series K) : K⟦ℝ⟧) = (tm i).series := fun i ↦ by
    rw [Subring.coe_mul, coe_single, mul_single_one_eq_translate,
      NormalForm.Term.series_eq_translate]
  -- Assemble the decomposition.
  refine ⟨⟨fun i ↦ (tm i).coefficient, fun i ↦ (tm i).exponent, rest, hprinc', ?_, hexp_nonpos,
    hexp_mono, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    rw [degree_eq_cantorDegree, hot_tm i, ← NatOrdinal.cantorDegree_of, ← NatOrdinal.val_natCast,
      ← NatOrdinal.wpow_def, NatOrdinal.cantorDegree_wpow]
  · rw [hcoe_rest, degree_lt_coe_iff_supportOrderType_lt_wpow, supportOrderType_list_sum hpairDrop,
      NatOrdinal.val_wpow, NatOrdinal.val_natCast]
    exact (Ordinal.isAdditivelyPrincipal_omega0_opow _).list_sum_lt fun a ha ↦ by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      exact hot_drop y hy
  · apply Subtype.ext
    rw [blockSum_def, Subring.coe_add, AddSubmonoidClass.coe_finsetSum]
    simp only [hpiece]
    change (b : K⟦ℝ⟧) = ∑ i, (tm i).series + ((b : K⟦ℝ⟧) - ∑ i, (tm i).series)
    abel
  · intro i j hij x hx y hy
    rw [hpiece] at hx hy
    exact (hbelow i j hij).lt hx hy
  · intro i x hx y hy
    rw [hpiece] at hx
    rw [hcoe_rest] at hy
    exact (hbelow_drop i).lt hx hy

end FLLM24

end
