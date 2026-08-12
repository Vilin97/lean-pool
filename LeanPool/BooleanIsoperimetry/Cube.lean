/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.IntervalCases

/-!
# Boolean cube basics

This file defines Boolean-cube vertices, Hamming distance, closed neighborhoods,
simplicial order, initial segments, slicing maps, and the Harper boundary
function `H`.
-/

open scoped BigOperators

namespace BooleanIsoperimetry

/-- A vertex of the `n`-dimensional Boolean cube, represented by its active coordinates. -/
abbrev Cube (n : ℕ) := Finset (Fin n)

/-- The Hamming distance between two Boolean-cube vertices. -/
noncomputable def hDist {n : ℕ} (x y : Cube n) : ℕ :=
  (symmDiff x y).card

/-- The closed Hamming `r`-neighborhood of a family of cube vertices. -/
noncomputable def neighborhood {n : ℕ} (r : ℕ) (A : Finset (Cube n)) : Finset (Cube n) :=
  Finset.univ.filter (fun v => ∃ u ∈ A, hDist u v ≤ r)

@[simp]
lemma mem_neighborhood_iff {n r : ℕ} {A : Finset (Cube n)} {v : Cube n} :
  v ∈ neighborhood r A ↔ ∃ u ∈ A, hDist u v ≤ r := by
  simp [neighborhood]

/-- The closed Hamming ball of radius `r` centered at the origin. -/
noncomputable def hammingBall {n : ℕ} (r : ℕ) : Finset (Cube n) :=
  Finset.univ.filter (fun v => v.card ≤ r)

/-- The binary encoding used to break ties in the simplicial order. -/
noncomputable def cubeToNat {n : ℕ} (x : Cube n) : ℕ :=
  ∑ i ∈ x, 2 ^ (i : ℕ)

/-- The non-strict simplicial order: first by weight, then by reverse binary order. -/
def simplicialLe {n : ℕ} (x y : Cube n) : Prop :=
  x.card < y.card ∨ (x.card = y.card ∧ cubeToNat y ≤ cubeToNat x)

/-- The strict simplicial order on Boolean-cube vertices. -/
def simplicialLt {n : ℕ} (x y : Cube n) : Prop :=
  simplicialLe x y ∧ ¬simplicialLe y x

-- ==========================================
-- BLOCK 1: INJECTIVITY OF ENCODING
-- ==========================================

lemma sum_pow_two_lt (n : ℕ) : (∑ i ∈ Finset.range n, 2^i) < 2^n := by
  rw [Nat.geomSum_eq] <;> norm_num

private lemma ofDigits_map_eq_sum (n : ℕ) (S : Finset ℕ) :
    Nat.ofDigits 2 (List.map (fun i => if i ∈ S then 1 else 0) (List.range n)) =
    ∑ i ∈ Finset.range n, (if i ∈ S then 2^i else 0) := by
  induction n with
  | zero =>
      simp
  | succ m ih =>
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        Nat.ofDigits_append, List.length_map, List.length_range, Nat.ofDigits_singleton,
        mul_ite, mul_one, mul_zero, Finset.range_add_one, Finset.sum_insert,
        Finset.mem_range, lt_self_iff_false, not_false_eq_true, ih]
      by_cases hm : m ∈ S <;> simp [hm]
      ring

lemma cubeToNat_inj {n : ℕ} {x y : Cube n} (h : cubeToNat x = cubeToNat y) : x = y := by
  revert x y
  have h_unique_binary :
      ∀ {x y : Finset ℕ}, x ⊆ Finset.range n → y ⊆ Finset.range n →
        (∑ i ∈ x, 2^i) = (∑ i ∈ y, 2^i) → x = y := by
    intros x y hx hy hsum_eq
    have h_binary_eq :
        (Nat.ofDigits 2 (List.map (fun i => if i ∈ x then 1 else 0) (List.range n))) =
          (Nat.ofDigits 2 (List.map (fun i => if i ∈ y then 1 else 0) (List.range n))) := by
      have h_binary_eq :
          (∑ i ∈ Finset.range n, (if i ∈ x then 2^i else 0)) =
            (∑ i ∈ Finset.range n, (if i ∈ y then 2^i else 0)) := by
        simp_all +decide only [Finset.sum_ite_mem]
        rw [Finset.inter_eq_right.mpr hx, Finset.inter_eq_right.mpr hy, hsum_eq]
      rw [ofDigits_map_eq_sum n x, ofDigits_map_eq_sum n y]
      exact h_binary_eq
    have h_binary_eq :
        List.map (fun i => if i ∈ x then 1 else 0) (List.range n) =
          List.map (fun i => if i ∈ y then 1 else 0) (List.range n) := by
      -- Little-endian binary representation is injective on bit lists of equal length.
      have h_ofDigits_inj :
          ∀ {l1 l2 : List ℕ}, (∀ i ∈ l1, i = 0 ∨ i = 1) →
            (∀ i ∈ l2, i = 0 ∨ i = 1) → List.length l1 = List.length l2 →
            Nat.ofDigits 2 l1 = Nat.ofDigits 2 l2 → l1 = l2 := by
        intro l1
        induction l1 with
        | nil =>
            intro l2 hl1 hl2 hlen hsum_eq
            cases l2 with
            | nil => rfl
            | cons d2 l2 => simp at hlen
        | cons d1 l1 ih =>
            intro l2 hl1 hl2 hlen hsum_eq
            cases l2 with
            | nil => simp at hlen
            | cons d2 l2 =>
                simp only [Nat.ofDigits, List.cons.injEq] at hsum_eq ⊢
                have hd1 : d1 = 0 ∨ d1 = 1 := hl1 d1 (by simp)
                have hd2 : d2 = 0 ∨ d2 = 1 := hl2 d2 (by simp)
                have htail_len : l1.length = l2.length := by simpa using hlen
                have htail_bits1 : ∀ i ∈ l1, i = 0 ∨ i = 1 := by
                  intro i hi
                  exact hl1 i (by simp [hi])
                have htail_bits2 : ∀ i ∈ l2, i = 0 ∨ i = 1 := by
                  intro i hi
                  exact hl2 i (by simp [hi])
                rcases hd1 with rfl | rfl <;> rcases hd2 with rfl | rfl
                all_goals
                  have htail_sum : Nat.ofDigits 2 l1 = Nat.ofDigits 2 l2 := by omega
                  exact ⟨ by omega, ih htail_bits1 htail_bits2 htail_len htail_sum ⟩
      exact h_ofDigits_inj
        (fun i hi => by
          rw [List.mem_map] at hi
          rcases hi with ⟨i, _, rfl⟩
          by_cases hi' : i ∈ x <;> simp +decide [hi'])
        (fun i hi => by
          rw [List.mem_map] at hi
          rcases hi with ⟨i, _, rfl⟩
          by_cases hi' : i ∈ y <;> simp +decide [hi'])
        (by simp +decide) ‹_›
    simp_all +decide
    grind
  intro x y hxy
  specialize @h_unique_binary (Finset.image (fun i : Fin n => (i : ℕ)) x)
    (Finset.image (fun i : Fin n => (i : ℕ)) y)
  simp_all +decide only [Finset.subset_iff, Finset.mem_image, Finset.mem_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Fin.is_lt, implies_true,
    forall_const]
  simp_all +decide only [Fin.val_injective.eq_iff, implies_true,
    Set.injOn_of_eq_iff_eq, Finset.sum_image]
  exact Finset.image_injective (fun a b h => by simpa [Fin.ext_iff] using h)
    (h_unique_binary hxy)

-- ==========================================
-- ORDER PROPERTIES
-- ==========================================

lemma simplicialLe_refl {n : ℕ} (a : Cube n) : simplicialLe a a := by
  unfold simplicialLe
  right
  exact ⟨rfl, le_rfl⟩

lemma simplicialLe_trans {n : ℕ} (a b c : Cube n)
    (hab : simplicialLe a b) (hbc : simplicialLe b c) : simplicialLe a c := by
  unfold simplicialLe at *
  rcases hab with hab_lt | ⟨hab_eq, hab_nat⟩
  · rcases hbc with hbc_lt | ⟨hbc_eq, _⟩
    · left; omega
    · left; omega
  · rcases hbc with hbc_lt | ⟨hbc_eq, hbc_nat⟩
    · left; omega
    · right
      constructor
      · omega
      · exact le_trans hbc_nat hab_nat

lemma simplicialLe_antisymm {n : ℕ} (a b : Cube n)
    (hab : simplicialLe a b) (hba : simplicialLe b a) : a = b := by
  unfold simplicialLe at hab hba
  rcases hab with h_a_lt_b | ⟨h_card_eq, h_nat_le⟩
  · rcases hba with h_b_lt_a | ⟨h_card_eq2, _⟩
    · omega
    · omega
  · rcases hba with h_b_lt_a | ⟨_, h_nat_le2⟩
    · omega
    · have h_nat_eq : cubeToNat a = cubeToNat b := le_antisymm h_nat_le2 h_nat_le
      exact cubeToNat_inj h_nat_eq

lemma simplicialLe_total {n : ℕ} (a b : Cube n) : simplicialLe a b ∨ simplicialLe b a := by
  unfold simplicialLe
  rcases lt_trichotomy a.card b.card with h_lt | h_eq | h_gt
  · left; left; exact h_lt
  · rcases le_total (cubeToNat a) (cubeToNat b) with h_nat_le | h_nat_ge
    · right; right; exact ⟨h_eq.symm, h_nat_le⟩
    · left; right; exact ⟨h_eq, h_nat_ge⟩
  · right; left; exact h_gt

-- ==========================================
-- 7. INITIAL SEGMENT
-- ==========================================

open Classical in
/-- The zero-based position of a vertex in the simplicial order. -/
noncomputable def rank {n : ℕ} (x : Cube n) : ℕ :=
  (Finset.univ.filter (fun y => simplicialLt y x)).card

open Classical in
/-- The first `k` vertices of the `n`-cube in simplicial order. -/
noncomputable def simplicialInitSeg (n : ℕ) (k : ℕ) : Finset (Cube n) :=
  Finset.univ.filter (fun x => rank x < k)

/-
Rank is bounded by the size of the cube.
-/
lemma rank_lt_two_pow {n : ℕ} (x : Cube n) : rank x < 2 ^ n := by
  classical
  have hlt : rank x < (Finset.univ : Finset (Cube n)).card := by
    apply Finset.card_lt_card
    apply Finset.filter_ssubset.mpr
    exact ⟨x, Finset.mem_univ _, fun h => h.2 <| by tauto⟩
  exact lt_of_lt_of_le hlt (by simp +decide [Finset.card_univ])

/-
Rank is strictly monotone for the strict simplicial order.
-/
lemma rank_strictMono {n : ℕ} {x y : Cube n} (h : simplicialLt x y) :
    rank x < rank y := by
  classical
  refine Finset.card_lt_card ?_
  simp only [Finset.ssubset_def, Finset.subset_iff, Finset.mem_filter, Finset.mem_univ,
    true_and]
  unfold simplicialLt at *
  unfold simplicialLe at *
  grind

lemma rank_lt_of_mem_simplicialInitSeg {n : ℕ} {k : ℕ} {x : Cube n}
    (hx : x ∈ simplicialInitSeg n k) :
    rank x < k := by
  classical
  unfold simplicialInitSeg at hx
  exact Finset.mem_filter.mp hx |>.2

/-
Rank is injective.
-/
lemma rank_injective {n : ℕ} : Function.Injective (@rank n) := by
  intros x y hxy
  by_contra h_neq
  -- Since $x \neq y$, by the total order property, either $x < y$ or $y < x$.
  have h_total : simplicialLt x y ∨ simplicialLt y x := by
    rcases simplicialLe_total x y with hle | hle
    · exact Or.inl ⟨hle, fun h => h_neq <| simplicialLe_antisymm _ _ hle h⟩
    · exact Or.inr ⟨hle, fun h => h_neq <| simplicialLe_antisymm _ _ h hle⟩
  obtain h | h := h_total
  · exact hxy.not_lt (rank_strictMono h)
  · exact hxy.not_gt (rank_strictMono h)

/-
The ranks are exactly 0, 1, ..., 2^n - 1.
-/
lemma rank_image_eq {n : ℕ} :
    Finset.univ.image (@rank n) = Finset.range (2 ^ n) := by
  fapply Finset.eq_of_subset_of_card_le
  · exact Finset.image_subset_iff.mpr fun x _ => Finset.mem_range.mpr (rank_lt_two_pow x)
  · rw [Finset.card_image_of_injective _ rank_injective]; simp +decide [Finset.card_univ]

/-
The cardinality of an initial segment.
-/
lemma card_simplicialInitSeg {n k : ℕ} :
    (simplicialInitSeg n k).card = min k (2 ^ n) := by
  rw [← Finset.card_image_of_injective _ (rank_injective)]
  rw [show Finset.image rank (simplicialInitSeg n k) =
    Finset.filter (· < k) (Finset.range (2 ^ n)) from ?_]
  · rw [show { x ∈ Finset.range (2 ^ n) | x < k } =
      Finset.range (Min.min k (2 ^ n)) by ext x; aesop]
    simp +decide
  · ext
    simp only [simplicialInitSeg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_range]
    constructor <;> intro h
    · exact ⟨ h.choose_spec.2 ▸ rank_lt_two_pow _, h.choose_spec.2 ▸ h.choose_spec.1 ⟩
    · obtain ⟨x, hx⟩ := Finset.mem_image.mp
        (rank_image_eq.symm ▸ Finset.mem_range.mpr h.1)
      use x
      aesop

-- ==========================================
-- 11. DIMENSIONAL SLICING (n → n + 1)
-- ==========================================

/-- Embed an `n`-cube vertex in dimension `n + 1` with last coordinate zero. -/
noncomputable def embed0 {n : ℕ} (x : Cube n) : Cube (n + 1) :=
  x.image Fin.castSucc

/-- Embed an `n`-cube vertex in dimension `n + 1` with last coordinate one. -/
noncomputable def embed1 {n : ℕ} (x : Cube n) : Cube (n + 1) :=
  insert (Fin.last n) (x.image Fin.castSucc)

/-- The lower slice of a family in dimension `n + 1`. -/
noncomputable def slice0 {n : ℕ} (A : Finset (Cube (n + 1))) : Finset (Cube n) :=
  Finset.univ.filter (fun x => embed0 x ∈ A)

/-- The upper slice of a family in dimension `n + 1`. -/
noncomputable def slice1 {n : ℕ} (A : Finset (Cube (n + 1))) : Finset (Cube n) :=
  Finset.univ.filter (fun x => embed1 x ∈ A)

/-
Lemma 11.1: Size of set equals sum of slice sizes
-/
lemma slice_card_add {n : ℕ} (A : Finset (Cube (n + 1))) :
    (slice0 A).card + (slice1 A).card = A.card := by
  -- Partition `A` by whether the last bit is present.
  have h_partition :
      A = Finset.image (fun x => x.image Fin.castSucc) (slice0 A) ∪
        Finset.image (fun x => insert (Fin.last n) (x.image Fin.castSucc)) (slice1 A) := by
    ext x
    by_cases hx : Fin.last n ∈ x <;>
      simp +decide only [slice0, slice1, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
    · constructor <;> intro h
      · refine Or.inr ⟨ Finset.univ.filter (fun i => Fin.castSucc i ∈ x), ?_, ?_ ⟩ <;>
          simp_all +decide only [Finset.ext_iff, embed1, Finset.mem_insert,
            Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        · convert h using 2; ext i; induction i using Fin.lastCases <;> aesop
        · intro a; induction a using Fin.lastCases <;> aesop
      · unfold embed0 embed1 at h; aesop
    · constructor
      · intro hx'
        refine Or.inl ⟨ Finset.univ.filter fun i => Fin.castSucc i ∈ x, ?_, ?_⟩
        · convert hx' using 1
          ext i; simp only [embed0, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨ fun ⟨ a, ha₁, ha₂ ⟩ => ha₂ ▸ ha₁,
            fun hi => by cases i using Fin.lastCases <;> aesop ⟩
        · ext i; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨ fun ⟨ a, ha, ha' ⟩ => ha'.symm ▸ ha,
            fun hi => by cases i using Fin.lastCases <;> aesop ⟩
      · rintro (⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩) <;>
          simp_all +decide only [embed0, embed1, Finset.mem_insert, Finset.mem_image,
            Fin.castSucc_ne_last, and_false, exists_false, not_false_eq_true, or_false,
            not_true_eq_false]
  convert congr_arg Finset.card h_partition.symm using 1
  rw [Finset.card_union_of_disjoint] <;> norm_num [Finset.disjoint_right]
  · rw [Finset.card_image_of_injective, Finset.card_image_of_injective] <;>
      norm_num [Function.Injective]
    · intro x y h
      ext i
      replace h := Finset.ext_iff.mp h (Fin.castSucc i)
      simp +decide at h
      tauto
    · exact fun x y h => Finset.image_injective (Fin.castSucc_injective _) h
  · intro a ha x hx H; replace H := Finset.ext_iff.mp H (Fin.last n) ; simp +decide at H

/-
==========================================
Helpers for neighborhood_succ
==========================================
-/
lemma hDist_embed0_embed0 {n : ℕ} (x y : Cube n) :
    hDist (embed0 x) (embed0 y) = hDist x y := by
  unfold hDist
  convert Finset.card_image_of_injective _ (Fin.castSucc_injective n) using 2; ext
  simp +decide only [symmDiff, Finset.sup_eq_union', Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_image]
  unfold embed0; aesop

lemma hDist_embed1_embed1 {n : ℕ} (x y : Cube n) :
    hDist (embed1 x) (embed1 y) = hDist x y := by
  unfold hDist embed1
  convert Finset.card_image_of_injective _ (Fin.castSucc_injective n) using 2
  ext
  simp +decide [symmDiff]
  aesop

lemma hDist_embed0_embed1 {n : ℕ} (x y : Cube n) :
    hDist (embed0 x) (embed1 y) = hDist x y + 1 := by
  unfold hDist
  -- Split the symmetric difference into old coordinates and the new last coordinate.
  have h_symmDiff :
      symmDiff (embed0 x) (embed1 y) =
        Finset.image Fin.castSucc (symmDiff x y) ∪ {Fin.last n} := by
    ext i
    obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
    · simp [embed0, embed1, Finset.mem_symmDiff, Finset.mem_image,
        (Fin.castSucc_injective n).eq_iff, (Fin.castSucc_lt_last j).ne]
    · simp [embed0, embed1, Finset.mem_symmDiff, Finset.mem_image,
        fun a : Fin n => (Fin.castSucc_lt_last a).ne]
  rw [h_symmDiff, Finset.card_union_of_disjoint] <;>
    norm_num [Finset.card_image_of_injective _ (Fin.castSucc_injective n)]

lemma slice0_neighborhood {n : ℕ} (A : Finset (Cube (n + 1))) :
    slice0 (neighborhood 1 A) = neighborhood 1 (slice0 A) ∪ slice1 A := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, huA, hu⟩ : ∃ u ∈ A, hDist u (embed0 x) ≤ 1 := by
      unfold slice0 at hx; unfold neighborhood at hx; aesop
    by_cases hlast : Fin.last n ∈ u
    · -- If Fin.last n ∈ u, write u = embed1 w with w ∈ slice1 A.
      obtain ⟨w, hw⟩ : ∃ w : Cube n, u = embed1 w := by
        use Finset.univ.filter (fun i => Fin.castSucc i ∈ u)
        ext i; simp only [embed1, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨ fun hi => or_iff_not_imp_left.mpr fun hi' =>
          ⟨ ⟨ i.val, lt_of_le_of_ne (Fin.le_last _) (by simpa [Fin.ext_iff] using hi') ⟩,
            by simpa [Fin.ext_iff] using hi, rfl ⟩,
          fun hi => hi.elim (fun hi => hi.symm ▸ hlast)
            fun ⟨ a, ha, ha' ⟩ => ha'.symm ▸ ha ⟩
      have h_dist : hDist (embed1 w) (embed0 x) = hDist w x + 1 := by
        convert hDist_embed0_embed1 x w using 1
        · exact congr_arg Finset.card (by ext; simp +decide [symmDiff_comm])
        · unfold hDist; simp +decide [symmDiff_comm]
      simp_all +decide only [hDist, Finset.mem_union, mem_neighborhood_iff,
        add_le_iff_nonpos_left, nonpos_iff_eq_zero, Finset.card_eq_zero,
        Finset.symmDiff_eq_empty, symmDiff_self, Finset.bot_eq_empty,
        Finset.card_empty, zero_add]
      exact Or.inr (Finset.mem_filter.mpr ⟨ Finset.mem_univ _, huA ⟩)
    · -- Since $Fin.last n \notin u$, we can write $u = embed0 w$ for some $w \in Cube n$.
      obtain ⟨w, hw⟩ : ∃ w : Cube n, u = embed0 w := by
        use Finset.univ.filter (fun i => Fin.castSucc i ∈ u)
        ext i; simp [embed0]
        induction i using Fin.lastCases <;> aesop
      simp_all +decide only [hDist_embed0_embed0, Finset.mem_union, mem_neighborhood_iff]
      exact Or.inl ⟨ w, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, huA ⟩, hu ⟩
  · simp only [neighborhood, slice0, Finset.mem_filter, Finset.mem_univ, true_and,
      slice1, Finset.mem_union]
    rintro (⟨ u, hu, hu' ⟩ | hu)
    · exact ⟨ _, hu, by rwa [hDist_embed0_embed0] ⟩
    · refine ⟨_, hu, ?_⟩
      simp +decide [hDist, embed0, embed1]
      simp +decide [symmDiff]

lemma slice1_neighborhood {n : ℕ} (A : Finset (Cube (n + 1))) :
    slice1 (neighborhood 1 A) = neighborhood 1 (slice1 A) ∪ slice0 A := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, huA, hu⟩ : ∃ u ∈ A, hDist u (embed1 v) ≤ 1 := by
      unfold slice1 at hv; aesop
    by_cases hlast : Fin.last n ∈ u
    · -- If Fin.last n ∈ u, write u = embed1 w with w ∈ slice1 A.
      obtain ⟨w, hw⟩ : ∃ w : Cube n, u = embed1 w := by
        use Finset.univ.filter (fun i : Fin n => Fin.castSucc i ∈ u)
        ext i
        simp only [embed1, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨ fun hi =>
          if hi' : i = Fin.last n then Or.inl hi' else
            Or.inr ⟨ ⟨ i.val,
              lt_of_le_of_ne (Fin.le_last _) (by simpa [Fin.ext_iff] using hi') ⟩,
              by simpa [Fin.ext_iff] using hi, rfl ⟩,
          fun hi => hi.elim (fun hi => hi.symm ▸ hlast)
            fun ⟨ a, ha, ha' ⟩ => ha'.symm ▸ ha ⟩
      simp_all +decide only [hDist_embed1_embed1, Finset.mem_union, mem_neighborhood_iff]
      exact Or.inl ⟨ w, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, huA ⟩, hu ⟩
    · -- Since $Fin.last n \notin u$, we can write $u = embed0 w$ for some $w \in Cube n$.
      obtain ⟨w, hw⟩ : ∃ w : Cube n, u = embed0 w := by
        use Finset.univ.filter (fun i => Fin.castSucc i ∈ u)
        ext i; simp only [embed0, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨ fun hi => by cases i using Fin.lastCases <;> aesop,
          fun ⟨ a, ha, ha' ⟩ => ha'.symm ▸ ha ⟩
      simp_all +decide only [hDist_embed0_embed1, add_le_iff_nonpos_left,
        nonpos_iff_eq_zero, Finset.mem_union, mem_neighborhood_iff]
      simp_all +decide only [hDist, Finset.card_eq_zero, Finset.symmDiff_eq_empty]
      exact Or.inr (Finset.mem_filter.mpr ⟨ Finset.mem_univ _, huA ⟩)
  · simp +zetaDelta only [Finset.mem_union, mem_neighborhood_iff] at *
    rintro (⟨ u, hu, huv ⟩ | hv) <;>
      simp_all +decide only [slice0, slice1, Finset.mem_filter, Finset.mem_univ,
        true_and, neighborhood]
    · use embed1 u, hu; simp_all +decide [hDist_embed1_embed1]
    · use embed0 v, hv, by
        rw [hDist_embed0_embed1]; norm_num
        unfold hDist; aesop

/-
Lemma 11.2: Boundary Decomposition
-/
lemma neighborhood_succ {n : ℕ} (A : Finset (Cube (n + 1))) :
    (neighborhood 1 A).card =
    (neighborhood 1 (slice0 A) ∪ slice1 A).card +
    (neighborhood 1 (slice1 A) ∪ slice0 A).card := by
  rw [← slice_card_add, slice0_neighborhood, slice1_neighborhood]

-- ==========================================
-- Helpers for initial_segment_optimal
-- ==========================================

/-- The size of the radius-one neighborhood of the simplicial initial segment of size `k`. -/
noncomputable def H (n k : ℕ) : ℕ :=
  (neighborhood 1 (simplicialInitSeg n k)).card

-- Basic algebraic properties of H
lemma H_zero (n : ℕ) : H n 0 = 0 := by
  simp [H, simplicialInitSeg, neighborhood]

lemma H_mono {n a b : ℕ} (h : a ≤ b) : H n a ≤ H n b := by
  unfold H
  apply Finset.card_le_card
  intro v hv
  rw [mem_neighborhood_iff] at hv ⊢
  rcases hv with ⟨u, hu, huv⟩
  refine ⟨u, ?_, huv⟩
  simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact Nat.lt_of_lt_of_le hu h

lemma H_le_cube (n k : ℕ) : H n k ≤ 2 ^ n := by
  have h : (neighborhood 1 (simplicialInitSeg n k)).card ≤ Fintype.card (Cube n) :=
    Finset.card_le_univ _
  simpa [H, Cube, Fintype.card_finset] using h

lemma H_ge_self (n k : ℕ) (hk : k ≤ 2 ^ n) : k ≤ H n k := by
  exact le_trans (by simp +decide [card_simplicialInitSeg, hk]) <|
    Finset.card_mono <| show simplicialInitSeg n k ⊆ neighborhood 1 (simplicialInitSeg n k) from
      fun x hx => by
        rw [mem_neighborhood_iff]
        exact ⟨x, hx, by simp +decide [hDist]⟩

lemma H_full (n : ℕ) : H n (2 ^ n) = 2 ^ n := by
  exact le_antisymm (H_le_cube n (2 ^ n)) (H_ge_self n (2 ^ n) (le_rfl))

-- Translation of set unions to algebraic maximums
lemma initSeg_nested {n : ℕ} {k m : ℕ} (h : k ≤ m) :
    simplicialInitSeg n k ⊆ simplicialInitSeg n m := by
  intro x hx
  simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact Nat.lt_of_lt_of_le hx h

lemma card_initSeg_union {n a b : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) :
    (simplicialInitSeg n a ∪ simplicialInitSeg n b).card = max a b := by
  cases le_total a b <;>
    simp_all +decide only [initSeg_nested, Finset.union_eq_right.mpr, sup_of_le_right,
      sup_of_le_left]
  · rw [card_simplicialInitSeg, min_eq_left hb]
  · rw [Finset.union_eq_left.mpr (initSeg_nested ‹_›), card_simplicialInitSeg]; aesop

/-
==========================================
Order-ideal characterization of neighborhoods
==========================================

Rank is monotone for the (non-strict) simplicial order.
-/
lemma rank_mono {n : ℕ} {a b : Cube n} (h : simplicialLe a b) : rank a ≤ rank b := by
  by_cases hab : a = b
  · rw [hab]
  · -- If `a ≠ b`, antisymmetry turns `simplicialLe a b` into strict order.
    have h_lt : simplicialLt a b := by
      exact ⟨ h, fun h' => hab <| simplicialLe_antisymm _ _ h h' ⟩
    exact le_of_lt (rank_strictMono h_lt)

/-- Remove the least active coordinate, giving the lowest-rank vertex in the closed unit ball. -/
noncomputable def gShift {n : ℕ} (v : Cube n) : Cube n :=
  if h : v.Nonempty then v.erase (v.min' h) else v

/-
gShift stays inside the closed radius-1 Hamming ball.
-/
lemma hDist_gShift_le {n : ℕ} (v : Cube n) : hDist (gShift v) v ≤ 1 := by
  unfold hDist gShift
  split_ifs
  · simp_all +decide only [symmDiff, Finset.sup_eq_union']
    simp +decide only [Finset.min'_mem, Finset.sdiff_erase, sdiff_self,
      Finset.bot_eq_empty, insert_empty_eq, Finset.union_singleton, Finset.mem_sdiff,
      Finset.mem_erase, ne_eq, not_true_eq_false, and_true, and_self,
      not_false_eq_true, Finset.card_insert_of_notMem, add_le_iff_nonpos_left, nonpos_iff_eq_zero,
      Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
    exact Finset.erase_subset _ _
  · simp_all +decide only [Finset.not_nonempty_iff_eq_empty, symmDiff, sdiff_self,
      Finset.bot_eq_empty,
      le_refl, sup_of_le_left, Finset.card_empty, zero_le]

/-
gShift is the smallest element (in simplicial order) of the closed Hamming ball.
-/
lemma gShift_le_ball {n : ℕ} {u v : Cube n} (h : hDist u v ≤ 1) :
    simplicialLe (gShift v) u := by
  obtain h | h := h.eq_or_lt
  · simp_all +decide only [le_refl]
    -- Distance one means one side erases a single coordinate from the other.
    obtain ⟨c, hc⟩ : ∃ c, (u = v.erase c ∧ c ∈ v) ∨ (v = u.erase c ∧ c ∈ u) := by
      obtain ⟨ c, hc ⟩ := Finset.card_eq_one.mp h
      use c
      simp_all +decide [Finset.ext_iff, symmDiff]
      grind
    obtain hc | hc := hc
    · simp_all +decide only [simplicialLe, Finset.card_erase_of_mem]
      -- Since c ∈ v, gShift v = v.erase (v.min' ·).
      have h_gShift_v : gShift v = v.erase (v.min' (by
      exact ⟨ c, hc.2 ⟩)) := by
        unfold gShift; aesop
      generalize_proofs at *
      by_cases h_cases : c = v.min' ‹_›
      · simp_all +decide only [Finset.card_erase_of_mem, lt_self_iff_false, le_refl,
          and_self, or_true]
      · simp_all +decide only
        refine Or.inr ⟨ ?_, ?_ ⟩
        · exact Finset.card_erase_of_mem (Finset.min'_mem _ ‹_›)
        · unfold cubeToNat
          rw [← Finset.sum_erase_add _ _
              (Finset.mem_erase_of_ne_of_mem (Ne.symm h_cases) (Finset.min'_mem _ ‹_›) ),
            ← Finset.sum_erase_add _ _ (Finset.mem_erase_of_ne_of_mem h_cases hc.2)]
          rw [Finset.erase_right_comm]
          exact Nat.add_le_add_left
            (pow_le_pow_right₀ (by decide) (Finset.min'_le _ _ hc.2) ) _
    · simp_all +decide only [simplicialLe]
      unfold gShift
      grind +suggestions
  · simp_all +decide only [Nat.lt_one_iff, zero_le]
    simp_all +decide only [hDist, Finset.card_eq_zero, Finset.symmDiff_eq_empty]
    unfold gShift
    by_cases hv : v.Nonempty
    · simp_all +decide only [simplicialLe, ↓reduceDIte]
      exact Or.inl (Finset.card_lt_card (Finset.erase_ssubset (Finset.min'_mem _ hv) ))
    · simp_all +decide only [Finset.not_nonempty_iff_eq_empty, simplicialLe,
        Finset.not_nonempty_empty,
        ↓reduceDIte, Finset.card_empty, lt_self_iff_false, le_refl, and_self, or_true]

/-
Membership in the neighborhood of an initial segment is governed by gShift.
-/
lemma mem_neighborhood_initSeg_iff {n k : ℕ} {v : Cube n} :
    v ∈ neighborhood 1 (simplicialInitSeg n k) ↔ rank (gShift v) < k := by
  by_contra h_neq
  contrapose! h_neq; constructor <;> intro h <;> simp_all +decide only [mem_neighborhood_iff]
  · obtain ⟨ u, hu₁, hu₂ ⟩ := h
    exact lt_of_le_of_lt (rank_mono <| gShift_le_ball hu₂) (Finset.mem_filter.mp hu₁ |>.2)
  · exact ⟨ gShift v, by unfold simplicialInitSeg; aesop, hDist_gShift_le v ⟩

/-
gShift preserves cardinality minus one (it removes exactly the minimum when nonempty).
-/
lemma card_gShift {n : ℕ} (v : Cube n) : (gShift v).card = v.card - 1 := by
  rcases Finset.eq_empty_or_nonempty v with (rfl | hne) <;>
    simp_all +decide only [gShift, Finset.not_nonempty_empty, ↓reduceDIte, Finset.card_empty,
      zero_tsub]
  exact Finset.card_erase_of_mem (Finset.min'_mem _ hne)

/-
Removing an element decreases the binary value by the corresponding power of two.
-/
lemma cubeToNat_erase {n : ℕ} {x : Cube n} {a : Fin n} (ha : a ∈ x) :
    cubeToNat x = cubeToNat (x.erase a) + 2 ^ (a : ℕ) := by
  unfold cubeToNat; rw [← Finset.sum_erase_add _ _ ha]

/-
If all active bits are below `M`, the binary value is below `2 ^ M`.
-/
lemma cubeToNat_lt_two_pow {n M : ℕ} {x : Cube n} (h : ∀ i ∈ x, (i : ℕ) < M) :
    cubeToNat x < 2 ^ M := by
  -- The sum of the powers of 2 in x is bounded by the sum of the powers of 2 up to M-1.
  have h_sum_bound : ∑ i ∈ x, 2 ^ (i : ℕ) ≤ ∑ j ∈ Finset.range M, 2 ^ j := by
    exact le_trans
      (by
        rw [← Finset.sum_image (by
          intros a ha b hb hab
          exact Fin.ext <| by simpa using hab)])
      (Finset.sum_le_sum_of_subset <|
        Finset.image_subset_iff.mpr fun i hi => Finset.mem_range.mpr <| h i hi)
  generalize_proofs at *; (
  exact lt_of_le_of_lt h_sum_bound (Nat.geomSum_lt (by norm_num) (by aesop) ))

/-
gShift never increases the binary value.
-/
lemma cubeToNat_gShift_le {n : ℕ} (x : Cube n) : cubeToNat (gShift x) ≤ cubeToNat x := by
  unfold gShift; by_cases hx : x.Nonempty <;>
    simp_all +decide only [Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_empty,
      ↓reduceDIte, le_refl]
  exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)

/-
Peeling: gShift commutes with removing the maximum element (cardinality ≥ 2).
-/
lemma cubeToNat_gShift_erase_max {n : ℕ} {x : Cube n} (hx : x.Nonempty) (h2 : 2 ≤ x.card) :
    cubeToNat (gShift x) =
      cubeToNat (gShift (x.erase (x.max' hx))) + 2 ^ ((x.max' hx : ℕ)) := by
  by_cases hmax : (x.max' hx) ∈ gShift x
  · rw [cubeToNat_erase]
    focus congr! 1
    · congr! 1
      unfold gShift
      grind +suggestions
    · assumption
  · exfalso
    have h_shift : gShift x = x.erase (x.min' hx) := dite_eq_left hx
    rw [h_shift, Finset.mem_erase] at hmax
    have h_mem : x.max' hx ∈ x := Finset.max'_mem x hx
    have h_eq : x.max' hx = x.min' hx := by tauto
    have h_card : x.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have h1 : a = x.min' hx := le_antisymm (h_eq ▸ Finset.le_max' x a ha) (Finset.min'_le x a ha)
      have h2 : b = x.min' hx := le_antisymm (h_eq ▸ Finset.le_max' x b hb) (Finset.min'_le x b hb)
      rw [h1, h2]
    omega

/-
The arithmetic core: among equal-cardinality vertices, removing the minimum element is
monotone for the binary value `cubeToNat`.  Proved by induction on cardinality, peeling off
the common largest element.
-/
lemma cubeToNat_gShift_mono {n : ℕ} :
    ∀ (m : ℕ) (s t : Cube n), s.card = m → t.card = m → cubeToNat t ≤ cubeToNat s →
      cubeToNat (gShift t) ≤ cubeToNat (gShift s) := by
  -- We proceed by induction on $m$.
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
  intro s t hs ht h
  by_cases hm : m ≤ 1
  · interval_cases m <;>
      simp_all +decide only [not_lt_zero, not_isEmpty_of_nonempty, IsEmpty.forall_iff,
        implies_true, Finset.card_eq_zero, le_refl, Nat.lt_one_iff, Finset.card_eq_one]
    unfold gShift; aesop
  · -- Let Ms = s.max' (nonempty) and Mt = t.max'.
    obtain ⟨Ms, hMs⟩ : ∃ Ms, Ms ∈ s ∧ ∀ i ∈ s, i ≤ Ms := by
      exact ⟨ Finset.max' s (Finset.card_pos.mp (by linarith) ), Finset.max'_mem _ _,
        fun i hi => Finset.le_max' _ _ hi ⟩
    obtain ⟨Mt, hMt⟩ : ∃ Mt, Mt ∈ t ∧ ∀ i ∈ t, i ≤ Mt := by
      exact ⟨ Finset.max' t (Finset.card_pos.mp (by linarith) ), Finset.max'_mem _ _,
        fun i hi => Finset.le_max' _ _ hi ⟩
    by_cases hMtMs : Mt < Ms
    · -- The peeled form of `gShift s` contains the top term `2 ^ (Ms : ℕ)`.
      have h_cubeToNat_gShift_s : cubeToNat (gShift s) ≥ 2 ^ (Ms : ℕ) := by
        rw [cubeToNat_gShift_erase_max]
        any_goals exact Finset.card_pos.mp (by linarith)
        · exact le_add_of_nonneg_of_le (Nat.zero_le _) (by
            rw [show Finset.max' s (Finset.card_pos.mp (by linarith) ) = Ms from
              le_antisymm (hMs.2 _ (Finset.max'_mem _ _) )
                (Finset.le_max' _ _ hMs.1)])
        · linarith
      -- By cubeToNat_lt_two_pow, cubeToNat t < 2^(Ms:ℕ).
      have h_cubeToNat_t : cubeToNat t < 2 ^ (Ms : ℕ) := by
        apply cubeToNat_lt_two_pow
        exact fun i hi => lt_of_le_of_lt (hMt.2 i hi) hMtMs
      exact le_trans (cubeToNat_gShift_le _) (by linarith)
    · by_cases hMsMt : Ms < Mt
      · have h_contra : cubeToNat s < 2 ^ (Mt : ℕ) := by
          apply cubeToNat_lt_two_pow
          exact fun i hi => lt_of_le_of_lt (hMs.2 i hi) hMsMt
        have h_contra : 2 ^ (Mt : ℕ) ≤ cubeToNat t := by
          have h_contra : cubeToNat t = cubeToNat (t.erase Mt) + 2 ^ (Mt : ℕ) := by
            exact cubeToNat_erase hMt.1
          exact h_contra.symm ▸ Nat.le_add_left _ _
        linarith
      · -- With `¬ Ms < Mt` and `¬ Mt < Ms` the two maxima coincide.
        obtain rfl : Ms = Mt := le_antisymm (not_lt.mp hMtMs) (not_lt.mp hMsMt)
        rw [not_le] at hm
        -- Apply the induction hypothesis after erasing the common maximum.
        have h_ind : cubeToNat (gShift (t.erase Ms)) ≤ cubeToNat (gShift (s.erase Ms)) := by
          apply ih (m - 1) (by
          exact Nat.pred_lt (ne_bot_of_gt hm)) (s.erase Ms) (t.erase Ms)
          · rw [Finset.card_erase_of_mem hMs.1, hs]
          · rw [Finset.card_erase_of_mem hMt.1, ht]
          · have h_erase :
                cubeToNat t = cubeToNat (t.erase Ms) + 2 ^ (Ms : ℕ) ∧
                  cubeToNat s = cubeToNat (s.erase Ms) + 2 ^ (Ms : ℕ) := by
              exact ⟨ cubeToNat_erase hMt.1, cubeToNat_erase hMs.1 ⟩
            linarith
        convert add_le_add_right h_ind (2 ^ (Ms : ℕ) ) using 1
        · rw [add_comm, cubeToNat_gShift_erase_max]
          focus
            rw [show Finset.max' t _ = Ms from
              le_antisymm (hMt.2 _ (Finset.max'_mem _ _) ) (Finset.le_max' _ _ hMt.1)]
          · exact ⟨ Ms, hMt.1 ⟩
          · grind
        · rw [add_comm, cubeToNat_gShift_erase_max]
          focus
            rw [show Finset.max' s _ = Ms from
              le_antisymm (hMs.2 _ (Finset.max'_mem _ _) ) (Finset.le_max' _ _ hMs.1)]
          · exact ⟨ Ms, hMs.1 ⟩
          · linarith

-- gShift is monotone for the simplicial order.
lemma gShift_monotone {n : ℕ} {w v : Cube n} (h : simplicialLe w v) :
    simplicialLe (gShift w) (gShift v) := by
  have hwv : w.card ≤ v.card := by rcases h with hlt | ⟨heq, _⟩ <;> omega
  have hgw := card_gShift w
  have hgv := card_gShift v
  by_cases hc : (gShift w).card < (gShift v).card
  · exact Or.inl hc
  · have hcardeq : (gShift w).card = (gShift v).card := by omega
    refine Or.inr ⟨hcardeq, ?_⟩
    by_cases hwc : w.card = v.card
    · rcases h with hlt | ⟨heq, hnat⟩
      · omega
      · exact cubeToNat_gShift_mono w.card w v rfl hwc.symm hnat
    · have hlt' : w.card < v.card := lt_of_le_of_ne hwv hwc
      have hw0 : (gShift w).card = 0 := by omega
      have hv0 : (gShift v).card = 0 := by omega
      rw [Finset.card_eq_zero] at hw0 hv0
      rw [hw0, hv0]

/-
A downward-closed set is an initial segment of its own cardinality.
-/
lemma downwardClosed_eq_initSeg {n : ℕ} {S : Finset (Cube n)}
    (hS : ∀ x y, simplicialLe x y → y ∈ S → x ∈ S) :
    S = simplicialInitSeg n S.card := by
  -- If $x \in S$, then by $hS$, we have $rank x < S.card$.
  have hS_rank : ∀ x ∈ S, rank x < S.card := by
    intro x hx
    have h_rank_lt : rank x < S.card := by
      refine Finset.card_lt_card ?_
      simp_all +decide only [Finset.ssubset_def, Finset.subset_iff, Finset.mem_filter,
        Finset.mem_univ, true_and, not_forall]
      exact ⟨ fun y hy => hS _ _ hy.1 hx, x, hx, by unfold simplicialLt; aesop ⟩
    exact h_rank_lt
  refine Finset.eq_of_subset_of_card_le
    (fun x hx ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS_rank x hx⟩)
    (by simp [card_simplicialInitSeg])

-- Structural theorem: The boundary of an initial segment is an initial segment
lemma neighborhood_initSeg_eq {n k : ℕ} :
    neighborhood 1 (simplicialInitSeg n k) = simplicialInitSeg n (H n k) := by
  have hdc : ∀ x y, simplicialLe x y → y ∈ neighborhood 1 (simplicialInitSeg n k) →
      x ∈ neighborhood 1 (simplicialInitSeg n k) := by
    intro x y hxy hy
    rw [mem_neighborhood_initSeg_iff] at hy ⊢
    exact lt_of_le_of_lt (rank_mono (gShift_monotone hxy)) hy
  exact downwardClosed_eq_initSeg hdc

/-
==========================================
The Algebraic Core of Harper's Theorem
==========================================

Embedding facts: embed0 preserves cardinality and binary value.
-/
lemma embed0_card {n : ℕ} (x : Cube n) : (embed0 x).card = x.card := by
  unfold embed0
  exact Finset.card_image_of_injective _ (Fin.castSucc_injective n)

lemma embed0_cubeToNat {n : ℕ} (x : Cube n) : cubeToNat (embed0 x) = cubeToNat x := by
  simp [cubeToNat, embed0]

/-
embed1 adds one element (the last coordinate) and the top power of two.
-/
lemma embed1_card {n : ℕ} (x : Cube n) : (embed1 x).card = x.card + 1 := by
  unfold embed1
  simp [Finset.card_image_of_injective _ (Fin.castSucc_injective n)]

lemma embed1_cubeToNat {n : ℕ} (x : Cube n) : cubeToNat (embed1 x) = cubeToNat x + 2 ^ n := by
  unfold cubeToNat embed1
  have hlast : Fin.last n ∉ Finset.image Fin.castSucc x := by
    intro h
    rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
    have hval : (i : ℕ) = n := by simpa using congrArg Fin.val hi
    exact Nat.ne_of_lt i.isLt hval
  rw [Finset.sum_insert hlast]
  rw [Finset.sum_image]
  · simp +decide only [Fin.val_last, Fin.val_castSucc]
    exact add_comm _ _
  · intro a _ b _ h
    exact Fin.castSucc_injective n h

/-
Both embeddings are monotone for the simplicial order.
-/
lemma embed0_mono {n : ℕ} {x y : Cube n} (h : simplicialLe x y) :
    simplicialLe (embed0 x) (embed0 y) := by
  unfold simplicialLe at *
  rw [embed0_card, embed0_card, embed0_cubeToNat, embed0_cubeToNat]; aesop

lemma embed1_mono {n : ℕ} {x y : Cube n} (h : simplicialLe x y) :
    simplicialLe (embed1 x) (embed1 y) := by
  unfold simplicialLe at *
  cases h <;> simp_all +decide [embed1_card, embed1_cubeToNat]

/-
The slices of an initial segment are themselves initial segments.
-/
lemma slice0_initSeg_eq {n k : ℕ} :
    slice0 (simplicialInitSeg (n + 1) k) =
      simplicialInitSeg n (slice0 (simplicialInitSeg (n + 1) k)).card := by
  apply downwardClosed_eq_initSeg; intro x y h_le h_mem; exact (by
  simp_all +decide only [simplicialInitSeg]
  simp_all +decide only [slice0, Finset.mem_filter, Finset.mem_univ, true_and]
  exact lt_of_le_of_lt (rank_mono (embed0_mono h_le) ) h_mem)

lemma slice1_initSeg_eq {n k : ℕ} :
    slice1 (simplicialInitSeg (n + 1) k) =
      simplicialInitSeg n (slice1 (simplicialInitSeg (n + 1) k)).card := by
  apply downwardClosed_eq_initSeg
  intro x y hxy hy
  simp_all +decide only [slice1, simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and]
  refine lt_of_le_of_lt ?_ hy
  apply rank_mono; exact embed1_mono hxy

/-
The boundary of an initial segment in dimension n+1, expressed via its slices.
-/
lemma H_succ_slice {n k : ℕ} :
    H (n + 1) k =
      max (H n (slice0 (simplicialInitSeg (n + 1) k)).card)
          (slice1 (simplicialInitSeg (n + 1) k)).card +
      max (H n (slice1 (simplicialInitSeg (n + 1) k)).card)
          (slice0 (simplicialInitSeg (n + 1) k)).card := by
  let A : Finset (Cube (n + 1)) := simplicialInitSeg (n + 1) k
  have hslice0 : slice0 A = simplicialInitSeg n (slice0 A).card := by
    simpa [A] using (slice0_initSeg_eq (n := n) (k := k))
  have hslice1 : slice1 A = simplicialInitSeg n (slice1 A).card := by
    simpa [A] using (slice1_initSeg_eq (n := n) (k := k))
  have hcard0 : (slice0 A).card ≤ 2 ^ n := by
    simpa using (Finset.card_le_univ (s := slice0 A))
  have hcard1 : (slice1 A).card ≤ 2 ^ n := by
    simpa using (Finset.card_le_univ (s := slice1 A))
  have h0 :
      (neighborhood 1 (slice0 A) ∪ slice1 A).card =
        max (H n (slice0 A).card) (slice1 A).card := by
    have hsets :
        neighborhood 1 (slice0 A) ∪ slice1 A =
          neighborhood 1 (simplicialInitSeg n (slice0 A).card) ∪
            simplicialInitSeg n (slice1 A).card :=
      congrArg₂ (· ∪ ·) (congrArg (neighborhood 1) hslice0) hslice1
    calc
      (neighborhood 1 (slice0 A) ∪ slice1 A).card =
          (neighborhood 1 (simplicialInitSeg n (slice0 A).card) ∪
            simplicialInitSeg n (slice1 A).card).card := congrArg Finset.card hsets
      _ = (simplicialInitSeg n (H n (slice0 A).card) ∪
            simplicialInitSeg n (slice1 A).card).card := by
            rw [neighborhood_initSeg_eq]
      _ = max (H n (slice0 A).card) (slice1 A).card :=
            card_initSeg_union (H_le_cube _ _) hcard1
  have h1 :
      (neighborhood 1 (slice1 A) ∪ slice0 A).card =
        max (H n (slice1 A).card) (slice0 A).card := by
    have hsets :
        neighborhood 1 (slice1 A) ∪ slice0 A =
          neighborhood 1 (simplicialInitSeg n (slice1 A).card) ∪
            simplicialInitSeg n (slice0 A).card :=
      congrArg₂ (· ∪ ·) (congrArg (neighborhood 1) hslice1) hslice0
    calc
      (neighborhood 1 (slice1 A) ∪ slice0 A).card =
          (neighborhood 1 (simplicialInitSeg n (slice1 A).card) ∪
            simplicialInitSeg n (slice0 A).card).card := congrArg Finset.card hsets
      _ = (simplicialInitSeg n (H n (slice1 A).card) ∪
            simplicialInitSeg n (slice0 A).card).card := by
            rw [neighborhood_initSeg_eq]
      _ = max (H n (slice1 A).card) (slice0 A).card :=
            card_initSeg_union (H_le_cube _ _) hcard0
  change (neighborhood 1 A).card =
    max (H n (slice0 A).card) (slice1 A).card +
      max (H n (slice1 A).card) (slice0 A).card
  rw [neighborhood_succ A, h0, h1]

-- ==========================================
-- MACAULAY / BINOMIAL CASCADE LAYER
-- ==========================================

/-- The sum of the first `r` binomial coefficients in row `n`. -/
def binomPrefix (n r : ℕ) : ℕ :=
  (Finset.range r).sum (fun i => Nat.choose n i)

/-- The binomial coefficient immediately preceding layer `r`, with value zero at `r = 0`. -/
def choosePred (n r : ℕ) : ℕ :=
  if r = 0 then 0 else Nat.choose n (r - 1)

end BooleanIsoperimetry
