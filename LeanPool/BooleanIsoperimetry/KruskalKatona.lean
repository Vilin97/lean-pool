/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import LeanPool.BooleanIsoperimetry.Macaulay

/-!
# Kruskal-Katona upper-shadow core

This file proves the set-family upper-shadow minimization theorem used by the
Boolean-isoperimetry argument.
-/

open scoped BigOperators
open scoped FinsetFamily

open Finset
open Finset.Colex

namespace BooleanIsoperimetry

/- # Kruskal–Katona upper-shadow core (relocated upstream of `Compression`).

This module carries the genuine set-family Kruskal–Katona theorem
`upperLayerShadow_min` and its numeric corollary `upperShadowVal_numeric_min`,
importing only `Cube` / `Cascade` / `Macaulay` (and Mathlib).  It is therefore
strictly upstream of `Compression.lean`, removing the previous import-wall that
forced the cross-slice cascade leaf to merely *reference* Kruskal–Katona without
being able to use it.  Relocated from the former `SetFamilyShadow.lean` (which is
now a thin re-export). -/

/-- The family of all `r`-element vertices in the `N`-cube. -/
def layer (N r : ℕ) : Finset (Cube N) :=
  Finset.univ.filter (fun x => x.card = r)

/-- Local numeric upper-shadow value (identical to `Shadow.upperShadow` but defined
here so the Kruskal–Katona core is strictly upstream of `Shadow.lean`):
`upperShadowVal N r t = H N (binomPrefix N r + t) - binomPrefix N (r+1)`. -/
noncomputable def upperShadowVal (N r t : ℕ) : ℕ :=
  H N (binomPrefix N r + t) - binomPrefix N (r + 1)

/-- The layer-`r` part of the simplicial initial segment with local size `t`. -/
noncomputable def layerInitSeg (N r t : ℕ) : Finset (Cube N) :=
  (simplicialInitSeg N (binomPrefix N r + t)).filter (fun x => x.card = r)

/-- The layer-`r + 1` upper shadow of a uniform family in layer `r`. -/
noncomputable def upperLayerShadow (N r : ℕ) (A : Finset (Cube N)) : Finset (Cube N) :=
  (Finset.upShadow A).filter (fun x => x.card = r + 1)

lemma binomPrefix_eq_card_lt (N r : ℕ) :
    binomPrefix N r = (Finset.univ.filter (fun (x : Cube N) => x.card < r)).card := by
  unfold binomPrefix
  have h_disj : (Finset.univ.filter (fun (x : Cube N) => x.card < r)) =
      Finset.biUnion (Finset.range r) (fun i => Finset.powersetCard i Finset.univ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    exact ⟨fun h => ⟨x.card, h, ⟨Finset.subset_univ x, rfl⟩⟩, fun ⟨i, hi, hpow⟩ => hpow.2 ▸ hi⟩
  rw [h_disj]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro i hi j hj hneq
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rw [Finset.mem_powersetCard] at hx hy
    omega

lemma mem_layerInitSeg_iff {N r t : ℕ} {x : Cube N} :
    x ∈ layerInitSeg N r t ↔ x.card = r ∧ rank x < binomPrefix N r + t := by
  simp [layerInitSeg, simplicialInitSeg]
  tauto

lemma layerInitSeg_card {N r t : ℕ} (ht : t ≤ Nat.choose N r) :
    (layerInitSeg N r t).card = t := by
  have hmem : ∀ x : Cube N,
      x ∈ layerInitSeg N r t ↔
        binomPrefix N r ≤ rank x ∧ rank x < binomPrefix N r + t := by
    intro x
    rw [mem_layerInitSeg_iff]
    constructor
    · rintro ⟨hcard, hrank⟩
      exact ⟨by simpa [hcard] using binomPrefix_card_le_rank x, hrank⟩
    · rintro ⟨hlo, hhi⟩
      have hlt_succ : rank x < binomPrefix N (r + 1) := by
        have hs : binomPrefix N r + t ≤ binomPrefix N (r + 1) := by
          rw [binomPrefix_succ]
          exact Nat.add_le_add_left ht _
        exact lt_of_lt_of_le hhi hs
      have hcard_lt_succ : x.card < r + 1 :=
        (rank_lt_binomPrefix_iff (n := N) (c := r + 1) x).mp hlt_succ
      have hnot_lt : ¬ x.card < r := by
        intro hxlt
        have hrank_lt : rank x < binomPrefix N r :=
          (rank_lt_binomPrefix_iff (n := N) (c := r) x).mpr hxlt
        exact not_lt_of_ge hlo hrank_lt
      exact ⟨by omega, hhi⟩
  have himage : Finset.image rank (layerInitSeg N r t)
      = Finset.Ico (binomPrefix N r) (binomPrefix N r + t) := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_image.mp hj with ⟨x, hx, rfl⟩
      exact Finset.mem_Ico.mpr ((hmem x).mp hx)
    · intro hj
      have hj' := Finset.mem_Ico.mp hj
      have hj_two : j < 2 ^ N := by
        have htop : binomPrefix N r + t ≤ binomPrefix N (r + 1) := by
          rw [binomPrefix_succ]
          exact Nat.add_le_add_left ht _
        exact lt_of_lt_of_le (lt_of_lt_of_le hj'.2 htop) (binomPrefix_le_two_pow N (r + 1))
      obtain ⟨x, hxrank⟩ := exists_rank_eq hj_two
      refine Finset.mem_image.mpr ⟨x, ?_, hxrank⟩
      exact (hmem x).mpr (by simpa [hxrank] using hj')
  rw [← Finset.card_image_of_injective _ rank_injective, himage]
  simp

lemma upperLayerShadow_sized {N r : ℕ} {A : Finset (Cube N)} {y : Cube N}
    (hy : y ∈ upperLayerShadow N r A) : y.card = r + 1 :=
  (Finset.mem_filter.mp hy).2

lemma neighborhood_binomPrefix {N r : ℕ} (hr : 1 ≤ r) :
    neighborhood 1 (simplicialInitSeg N (binomPrefix N r)) =
    simplicialInitSeg N (binomPrefix N (r + 1)) := by
  rw [neighborhood_initSeg_eq, H_binomPrefix N r hr]

lemma mem_layerInitSeg_iff_rank {N r t : ℕ} {x : Cube N} :
    x ∈ layerInitSeg N r t ↔
      x.card = r ∧ binomPrefix N r ≤ rank x ∧ rank x < binomPrefix N r + t := by
  simp only [layerInitSeg, simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hrank, hcard⟩
    exact ⟨hcard, by simpa [hcard] using binomPrefix_card_le_rank x, hrank⟩
  · rintro ⟨hcard, hrank⟩
    exact ⟨hrank.2, hcard⟩

lemma simplicialInitSeg_decomp {N r t : ℕ} (ht : t ≤ Nat.choose N r) :
    simplicialInitSeg N (binomPrefix N r + t) =
    (simplicialInitSeg N (binomPrefix N r)) ∪ layerInitSeg N r t := by
  ext x
  simp only [Finset.mem_union, mem_layerInitSeg_iff_rank, simplicialInitSeg, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hrank
    have h_card_le : x.card ≤ r := by
      by_contra! hgt
      have h_rank_ge : binomPrefix N (r + 1) ≤ rank x := by
        have h1 : ¬(x.card < r + 1) := by omega
        have h2 : ¬(rank x < binomPrefix N (r + 1)) :=
          mt (rank_lt_binomPrefix_iff (n := N) (c := r + 1) x).mp h1
        omega
      have h_rank_lt : binomPrefix N r + t ≤ binomPrefix N (r + 1) := by
        have h_eq : binomPrefix N r + Nat.choose N r = binomPrefix N (r + 1) :=
          (binomPrefix_succ N r).symm
        omega
      omega
    rcases lt_or_eq_of_le h_card_le with hlt | heq
    · left
      have h_rank_lt : rank x < binomPrefix N r :=
        (rank_lt_binomPrefix_iff (n := N) (c := r) x).mpr hlt
      exact h_rank_lt
    · right
      exact ⟨heq, by simpa [heq] using binomPrefix_card_le_rank x, hrank⟩
  · rintro (hlt | ⟨heq, _, hrank⟩)
    · omega
    · exact hrank

lemma upShadow_subset_neighborhood {N r : ℕ} (A : Finset (Cube N)) (_ : ∀ x ∈ A, x.card = r) :
    Finset.upShadow A ⊆ neighborhood 1 A := by
  intro x hx
  rw [Finset.mem_upShadow_iff] at hx
  obtain ⟨u, hu, a, ha, hins⟩ := hx
  rw [mem_neighborhood_iff]
  refine ⟨u, hu, ?_⟩
  have hone : hDist u x = 1 := by
    unfold hDist
    have hsd : symmDiff u x = {a} := by
      rw [← hins]
      ext y
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (⟨hyu, hni⟩ | ⟨hyi, hnu⟩)
        · exact absurd (Or.inr hyu) hni
        · rcases hyi with h | h
          · exact h
          · exact absurd h hnu
      · rintro rfl
        exact Or.inr ⟨Or.inl rfl, ha⟩
    rw [hsd]; simp
  omega

lemma hDist_eq_one_of_card_diff {N r : ℕ} {u x : Cube N} (hu : u.card = r)
    (hx : x.card = r + 1) (hd : hDist u x ≤ 1) :
    u ⊆ x ∧ (x \ u).card = 1 := by
  unfold hDist at hd
  have hsd : symmDiff u x = (u \ x) ∪ (x \ u) := by
    ext y
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  have hdisj : Disjoint (u \ x) (x \ u) := disjoint_sdiff_sdiff
  have hcard : (u \ x).card + (x \ u).card ≤ 1 := by
    rw [hsd, Finset.card_union_of_disjoint hdisj] at hd; exact hd
  have hkey : (x \ u).card + u.card = (u \ x).card + x.card := by
    have h1 : (x \ u).card + u.card = (x ∪ u).card := Finset.card_sdiff_add_card x u
    have h2 : (u \ x).card + x.card = (u ∪ x).card := Finset.card_sdiff_add_card u x
    rw [h1, h2, Finset.union_comm]
  rw [hu, hx] at hkey
  have hudiff : (u \ x).card = 0 := by omega
  have hsub : u ⊆ x := by
    rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]
    exact hudiff
  exact ⟨hsub, by omega⟩

lemma card_le_of_hDist_le_one {N r : ℕ} {u x : Cube N} (hu : u.card = r) (hd : hDist u x ≤ 1) :
    x.card ≤ r + 1 := by
  unfold hDist at hd
  have hsub : x \ u ⊆ symmDiff u x := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    rw [Finset.mem_symmDiff]
    exact Or.inr hy
  have hcard1 : (x \ u).card ≤ 1 := le_trans (Finset.card_mono hsub) hd
  have hx : x.card ≤ (x \ u).card + u.card := Finset.card_le_card_sdiff_add_card
  omega

lemma neighborhood_union {N r : ℕ} (A B : Finset (Cube N)) :
    neighborhood r (A ∪ B) = neighborhood r A ∪ neighborhood r B := by
  ext x
  simp [mem_neighborhood_iff, or_and_right, exists_or]

lemma upperShadowVal_eq_card_upperLayerShadow {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) :
    upperShadowVal N r t = (upperLayerShadow N r (layerInitSeg N r t)).card := by
  unfold upperShadowVal
  unfold H
  rw [simplicialInitSeg_decomp ht]
  rw [neighborhood_union]
  rw [neighborhood_binomPrefix hr]
  have h_disj : Disjoint (simplicialInitSeg N (binomPrefix N (r + 1)))
      (upperLayerShadow N r (layerInitSeg N r t)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [upperLayerShadow, Finset.mem_filter] at hy
    have h_card : x.card = r + 1 := hy.2
    have h_rank_ge : binomPrefix N (r + 1) ≤ rank x := by
      simpa [h_card] using binomPrefix_card_le_rank x
    omega
  have h_union : simplicialInitSeg N (binomPrefix N (r + 1)) ∪ neighborhood 1 (layerInitSeg N r t) =
      simplicialInitSeg N (binomPrefix N (r + 1)) ∪ upperLayerShadow N r (layerInitSeg N r t) := by
    ext x
    simp only [Finset.mem_union, upperLayerShadow, Finset.mem_filter]
    constructor
    · rintro (hx | hx_nb)
      · left; exact hx
      · have h_card_le : x.card ≤ r + 1 := by
          rcases mem_neighborhood_iff.mp hx_nb with ⟨u, hu, hdist⟩
          have h_u_card : u.card = r := by
            simp only [layerInitSeg, Finset.mem_filter] at hu
            exact hu.2
          exact card_le_of_hDist_le_one h_u_card hdist
        rcases lt_or_eq_of_le h_card_le with hlt | heq
        · left
          have h_rank_lt : rank x < binomPrefix N (r + 1) :=
            (rank_lt_binomPrefix_iff (n := N) (c := r + 1) x).mpr hlt
          simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h_rank_lt
        · right
          refine ⟨?_, heq⟩
          rw [Finset.mem_upShadow_iff]
          rcases mem_neighborhood_iff.mp hx_nb with ⟨u, hu, hdist⟩
          have h_u_card : u.card = r := by
            simp only [layerInitSeg, Finset.mem_filter] at hu
            exact hu.2
          rcases hDist_eq_one_of_card_diff h_u_card heq hdist with ⟨hsub, hdiff⟩
          have h_exists := Finset.card_eq_one.mp hdiff
          rcases h_exists with ⟨a, ha⟩
          have h_a_not_mem : a ∉ u := by
            have h_a_in : a ∈ x \ u := by rw [ha]; exact Finset.mem_singleton_self a
            exact (Finset.mem_sdiff.mp h_a_in).2
          have heq_insert : x = insert a u := by
            ext y
            constructor
            · intro hy
              by_cases hyu : y ∈ u
              · exact Finset.mem_insert_of_mem hyu
              · have h_y_in : y ∈ x \ u := Finset.mem_sdiff.mpr ⟨hy, hyu⟩
                rw [ha, Finset.mem_singleton] at h_y_in
                rw [h_y_in]
                exact Finset.mem_insert_self a u
            · rintro hy
              rcases Finset.mem_insert.mp hy with hy_eq | hyu
              · rw [hy_eq]
                have h_a_in : a ∈ x \ u := by rw [ha]; exact Finset.mem_singleton_self a
                exact (Finset.mem_sdiff.mp h_a_in).1
              · exact hsub hyu
          exact ⟨u, hu, a, h_a_not_mem, heq_insert.symm⟩
    · rintro (hx | ⟨hx_up, _⟩)
      · left; exact hx
      · right
        apply upShadow_subset_neighborhood (layerInitSeg N r t)
        · intro y hy
          simp only [layerInitSeg, Finset.mem_filter] at hy
          exact hy.2
        · exact hx_up
  rw [h_union]
  rw [Finset.card_union_of_disjoint h_disj]
  have h_card_simp :
      (simplicialInitSeg N (binomPrefix N (r + 1))).card = binomPrefix N (r + 1) := by
    rw [card_simplicialInitSeg]
    have h_le : binomPrefix N (r + 1) ≤ 2^N := binomPrefix_le_two_pow N (r + 1)
    omega
  rw [h_card_simp]
  omega

/-! ## Kruskal--Katona upper-shadow minimization in project language

The next theorem is the single-layer Macaulay/Kruskal--Katona input needed by
the Frankl--Füredi paired-compression layer.  It is deliberately stated with the
real set-family upper shadow `upperLayerShadow`, not the numerical
`upperShadow` wrapper.
-/

lemma upShadow_eq_upperLayerShadow_of_uniform {N r : ℕ} {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) :
    Finset.upShadow A = upperLayerShadow N r A := by
  ext y
  simp only [upperLayerShadow, Finset.mem_filter]
  constructor
  · intro hy
    refine ⟨hy, ?_⟩
    rw [Finset.mem_upShadow_iff_exists_mem_card_add_one] at hy
    rcases hy with ⟨x, hxA, _hxy, hcard⟩
    rw [hA x hxA] at hcard
    exact hcard
  · exact And.left

lemma upperLayerShadow_card_eq_shadow_compls {N r : ℕ} {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) :
    (upperLayerShadow N r A).card = (Finset.shadow Aᶜˢ).card := by
  rw [← upShadow_eq_upperLayerShadow_of_uniform hA]
  rw [Finset.shadow_compls, Finset.card_compls]

lemma layerInitSeg_uniform {N r t : ℕ} :
    ∀ x ∈ layerInitSeg N r t, x.card = r := by
  intro x hx
  simp only [layerInitSeg, Finset.mem_filter] at hx
  exact hx.2

lemma card_le_choose_of_uniform {N r : ℕ} {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) :
    A.card ≤ Nat.choose N r := by
  have hsub : A ⊆ Finset.univ.filter (fun x : Cube N => x.card = r) := by
    intro x hx
    simp [hA x hx]
  refine (Finset.card_mono hsub).trans_eq ?_
  rw [show Finset.univ.filter (fun x : Cube N => x.card = r) =
      Finset.powersetCard r (Finset.univ : Finset (Fin N)) by
    ext x
    simp [Finset.mem_powersetCard]]
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma cubeToNat_add_compl {N : ℕ} (A : Finset (Fin N)) :
    cubeToNat A + cubeToNat Aᶜ = cubeToNat (Finset.univ : Cube N) := by
  unfold cubeToNat
  exact sum_add_sum_compl A (fun (i:Fin N) => 2^(i:ℕ))

lemma cubeToNat_compl_lt_cubeToNat_compl {N : ℕ} {A B : Finset (Fin N)} :
    cubeToNat Aᶜ < cubeToNat Bᶜ ↔ cubeToNat B < cubeToNat A := by
  have hA := cubeToNat_add_compl A
  have hB := cubeToNat_add_compl B
  omega

lemma toColex_lt_iff_cubeToNat_lt {N : ℕ} {A B : Finset (Fin N)} :
    toColex A < toColex B ↔ cubeToNat A < cubeToNat B := by
  have h_image_A : cubeToNat A = ∑ i ∈ A.image (fun i : Fin N => (i:ℕ)), 2^i := by
    unfold cubeToNat
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact Fin.val_injective hxy
  have h_image_B : cubeToNat B = ∑ i ∈ B.image (fun i : Fin N => (i:ℕ)), 2^i := by
    unfold cubeToNat
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact Fin.val_injective hxy
  rw [h_image_A, h_image_B]
  rw [Finset.geomSum_lt_geomSum_iff_toColex_lt_toColex (by norm_num)]
  rw [Finset.Colex.toColex_image_lt_toColex_image]
  · intro x y hxy; exact hxy

lemma toColex_compl_lt_toColex_compl {N : ℕ} {A B : Finset (Fin N)} :
    toColex Aᶜ < toColex Bᶜ ↔ toColex B < toColex A := by
  rw [toColex_lt_iff_cubeToNat_lt, toColex_lt_iff_cubeToNat_lt]
  exact cubeToNat_compl_lt_cubeToNat_compl

/-- The complement of a simplicial layer initial segment is a colex initial
segment.  This is the remaining order-orientation bridge needed to feed the
project's layer initial segments into mathlib's lower-shadow Kruskal--Katona
theorem.

On a fixed Hamming layer, the project order takes larger binary/colex values
first; complementation changes a larger `r`-set value into a smaller
`(N-r)`-set value.  Thus complements of project initial segments are ordinary
colex initial segments. -/
lemma layerInitSeg_compls_isInitSeg {N r t : ℕ} (_ : t ≤ Nat.choose N r) :
    Finset.Colex.IsInitSeg (layerInitSeg N r t)ᶜˢ (N - r) := by
  unfold Finset.Colex.IsInitSeg
  constructor
  · intro x hx
    simp only [mem_coe, mem_compls, mem_layerInitSeg_iff] at hx
    have h_card := hx.1
    have h1 : x.card + xᶜ.card = Fintype.card (Fin N) := Finset.card_add_card_compl x
    rw [Fintype.card_fin, h_card] at h1
    have h2 := Finset.card_le_univ xᶜ
    rw [Fintype.card_fin, h_card] at h2
    omega
  · rintro s u hs ⟨hlt, hcard⟩
    simp only [mem_compls, mem_layerInitSeg_iff] at hs ⊢
    have h_s_card : sᶜ.card = r := hs.1
    have hrN : r ≤ N := by
      have := Finset.card_le_univ sᶜ
      rw [Fintype.card_fin, h_s_card] at this
      exact this
    have h1 : u.card + uᶜ.card = Fintype.card (Fin N) := Finset.card_add_card_compl u
    rw [Fintype.card_fin, hcard] at h1
    have hu_card_c : uᶜ.card = r := by omega
    refine ⟨hu_card_c, ?_⟩
    have hlt_colex : toColex u < toColex s := hlt
    have h_colex_c : toColex sᶜ < toColex uᶜ := toColex_compl_lt_toColex_compl.mpr hlt_colex
    have h_c_lt : cubeToNat sᶜ < cubeToNat uᶜ := toColex_lt_iff_cubeToNat_lt.mp h_colex_c
    have h_simp : simplicialLt uᶜ sᶜ := by
      unfold simplicialLt simplicialLe
      have hc : uᶜ.card = sᶜ.card := by omega
      refine ⟨Or.inr ⟨hc, by omega⟩, ?_⟩
      rintro (h2 | ⟨h3, h4⟩)
      · omega
      · omega
    have h_rank : rank uᶜ < rank sᶜ := rank_strictMono h_simp
    omega

/-- **Upper-shadow Kruskal--Katona target.**  Among all `r`-uniform families in
the `N`-cube with the same cardinality, the simplicial layer initial segment has
minimum upper shadow in layer `r+1`.

This is the project-language form of the mathlib KK theorem transported from
lower shadows through complementation, with the fixed-card simplicial order
identified with the corresponding colex/opposite-colex layer order. -/
theorem upperLayerShadow_min {N r : ℕ} {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) :
    (upperLayerShadow N r (layerInitSeg N r A.card)).card ≤
      (upperLayerShadow N r A).card := by
  rw [upperLayerShadow_card_eq_shadow_compls layerInitSeg_uniform,
      upperLayerShadow_card_eq_shadow_compls hA]
  refine Finset.kruskal_katona (r := N - r) ?hA ?hcard ?hinit
  · intro x hx
    change x ∈ Aᶜˢ at hx
    rw [Finset.mem_compls] at hx
    rw [← compl_compl x, Finset.card_compl, hA xᶜ hx, Fintype.card_fin]
  · rw [Finset.card_compls, Finset.card_compls,
      layerInitSeg_card (card_le_choose_of_uniform hA)]
  · exact layerInitSeg_compls_isInitSeg (N := N) (r := r) (t := A.card)
      (card_le_choose_of_uniform hA)

/-- Numeric corollary of `upperLayerShadow_min`: the numerical scaffold
`upperShadow` is bounded by the actual upper shadow of every same-size
`r`-uniform family. -/
theorem upperShadowVal_numeric_min {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) (hcard : A.card = t) :
    upperShadowVal N r t ≤ (upperLayerShadow N r A).card := by
  rw [upperShadowVal_eq_card_upperLayerShadow hr ht, ← hcard]
  exact upperLayerShadow_min hA

end BooleanIsoperimetry
