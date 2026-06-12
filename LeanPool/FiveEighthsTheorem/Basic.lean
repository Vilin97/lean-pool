/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.CommutingProbability
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The 5/8 theorem

If `G` is a nonabelian group, then its Mathlib commuting probability is at most `5/8`.
For infinite groups this is immediate because `commProb` is defined to be `0`; the substantive
finite case is the theorem of Gustafson, *What is the probability that two group elements
commute?* (Amer. Math. Monthly 80, 1973), and the bound is attained (e.g. by the quaternion
group of order 8).

The proof is the classical counting argument:

* If `G` is nonabelian then `G ⧸ Z(G)` is not cyclic, so the index of the center is not `1`
  or a prime; hence `|Z(G)| / |G| ≤ 1/4`.
* For `g ∉ Z(G)` the centralizer of `g` is a proper subgroup, so `|C(g)| / |G| ≤ 1/2`.
* Summing `|C(g)|` over `g ∈ G` counts the commuting pairs, and splitting the sum over
  `Z(G)` and its complement gives
  `commProb G ≤ z + (1 - z) / 2 ≤ 1/2 + (1/4)/2 = 5/8`, where `z = |Z(G)| / |G|`.

## Main results

* `FiveEighths.commProb_le_five_eighths`: the commuting probability of a nonabelian group is at
  most `5/8`.
* `FiveEighths.centralFraction_le_quarter`: the center of a finite nonabelian group contains
  at most a quarter of its elements.
* `FiveEighths.centralizerFraction_le_half`: the centralizer of a noncentral element contains
  at most half of the elements.

All declarations live in the `FiveEighths` namespace.
-/

namespace FiveEighths

/-- The fraction of elements of a finite group `G` that lie in its center. -/
noncomputable def centralFraction (G : Type*) [Group G] : ℚ :=
  (Nat.card (Subgroup.center G) : ℚ) / (Nat.card G : ℚ)

/-- The fraction of elements of a finite group that commute with a given element `g`. -/
noncomputable def centralizerFraction {G : Type*} [Group G] (g : G) : ℚ :=
  (Nat.card (Subgroup.centralizer {g} : Subgroup G) : ℚ) / (Nat.card G : ℚ)

variable {G : Type*} [Group G]

private theorem card_div_card_eq_one_div_index [Finite G] (H : Subgroup G) :
    (Nat.card H : ℚ) / (Nat.card G : ℚ) = 1 / (H.index : ℚ) := by
  have hG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hindex : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [div_eq_div_iff (by exact_mod_cast hG) (by exact_mod_cast hindex), one_mul]
  exact_mod_cast Subgroup.card_mul_index H

theorem centralFraction_eq_one_div_index [Finite G] :
    centralFraction G = 1 / ((Subgroup.center G).index : ℚ) :=
  card_div_card_eq_one_div_index (Subgroup.center G)

/-- If `G` is nonabelian then `G ⧸ Z(G)` is not cyclic, so the index of the center cannot be
prime. -/
theorem center_index_ne_prime (h : ¬IsMulCommutative G) {p : ℕ} (hp : p.Prime) :
    (Subgroup.center G).index ≠ p := by
  intro heq
  have hcard : Nat.card (G ⧸ Subgroup.center G) = p := heq
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (G ⧸ Subgroup.center G) := isCyclic_of_prime_card hcard
  exact h (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (QuotientGroup.mk' (Subgroup.center G)) (QuotientGroup.ker_mk' _).le)

/-- The center of a finite nonabelian group has index at least `4`: the index is nonzero by
finiteness, is not `1` by noncommutativity, and is not `2` or `3` because those are prime. -/
theorem four_le_center_index [Finite G] (h : ¬IsMulCommutative G) :
    4 ≤ (Subgroup.center G).index := by
  have h0 : (Subgroup.center G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (Subgroup.center G).index ≠ 1 := fun h1 =>
    h (Subgroup.center_eq_top_iff.mp (Subgroup.index_eq_one.mp h1))
  have h2 := center_index_ne_prime h Nat.prime_two
  have h3 := center_index_ne_prime h Nat.prime_three
  omega

/-- The center of a finite nonabelian group contains at most a quarter of its elements. -/
theorem centralFraction_le_quarter [Finite G] (h : ¬IsMulCommutative G) :
    centralFraction G ≤ 1 / 4 := by
  have h4 := four_le_center_index h
  rw [centralFraction_eq_one_div_index,
    div_le_div_iff₀ (by exact_mod_cast by omega : (0 : ℚ) < (Subgroup.center G).index)
      (by norm_num : (0 : ℚ) < 4), one_mul, one_mul]
  exact_mod_cast h4

/-- The centralizer of a noncentral element is a proper subgroup, so its index is at
least `2`. -/
theorem two_le_centralizer_index [Finite G] {g : G} (hg : g ∉ Subgroup.center G) :
    2 ≤ (Subgroup.centralizer {g} : Subgroup G).index := by
  have h0 : (Subgroup.centralizer {g} : Subgroup G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hne_top : (Subgroup.centralizer {g} : Subgroup G) ≠ ⊤ := by
    intro hc
    exact hg (Subgroup.mem_center_iff.mpr fun k =>
      Subgroup.mem_centralizer_singleton_iff.mp (hc ▸ Subgroup.mem_top k))
  have h1 : (Subgroup.centralizer {g} : Subgroup G).index ≠ 1 := fun h1 =>
    hne_top (Subgroup.index_eq_one.mp h1)
  omega

/-- The centralizer of a noncentral element contains at most half of the elements. -/
theorem centralizerFraction_le_half [Finite G] {g : G} (hg : g ∉ Subgroup.center G) :
    centralizerFraction g ≤ 1 / 2 := by
  have h2 := two_le_centralizer_index hg
  rw [centralizerFraction, card_div_card_eq_one_div_index,
    div_le_div_iff₀
      (by exact_mod_cast by omega : (0 : ℚ) < ((Subgroup.centralizer {g} : Subgroup G).index))
      (by norm_num : (0 : ℚ) < 2), one_mul, one_mul]
  exact_mod_cast h2

private theorem ncard_setOf_pair_eq_sum {α : Type*} [Fintype α] (p : α → α → Prop) :
    Set.ncard { (g, h) | p g h } = ∑ g, Set.ncard { h | p g h } := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr (Equiv.setProdEquivSigma _), Nat.card_sigma]
  simp_rw [Nat.card_coe_set_eq]
  rfl

private theorem ncard_le_ncard_univ {α : Type*} [Finite α] (p : α → Prop) :
    Set.ncard { g | p g } ≤ Set.ncard (Set.univ : Set α) :=
  Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ

/-- The commuting probability of `G` counts the commuting pairs of elements. -/
theorem commProb_eq_ncard_div_sq (G : Type*) [Group G] :
    commProb G = (Set.ncard { (g, h) : G × G | g * h = h * g } : ℚ) / (Nat.card G : ℚ) ^ 2 := by
  have key : Nat.card { p : G × G // Commute p.1 p.2 }
      = Set.ncard { (g, h) : G × G | g * h = h * g } := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun p => Iff.rfl)
  rw [commProb_def, key]

/-- The cardinality of a type, as a rational number (zero if the type is infinite). -/
noncomputable abbrev typeQCard (G : Type*) : ℚ := Nat.card G

/-- The cardinality of a set, as a rational number (zero if the set is infinite). -/
noncomputable def setQCard {α : Type*} (s : Set α) : ℚ := s.ncard

local notation:max "#ₜ" G:max => typeQCard G
local notation:max "#ₛ" s:max => setQCard s
local notation "Z(" G ")" => Subgroup.center G

private theorem commProb_le_five_eighths_of_finite (G : Type*) [Group G] [Finite G]
    (h : ¬IsMulCommutative G) : commProb G ≤ 5 / 8 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  calc
    commProb G
    _ = #ₛ{ (g, h) : G × G | g * h = h * g } / #ₜG ^ 2 := by
        unfold setQCard
        exact commProb_eq_ncard_div_sq G
    _ = (∑ g, #ₛ{ h | g * h = h * g }) / #ₜG ^ 2 := by
        congr 1
        unfold setQCard
        exact_mod_cast ncard_setOf_pair_eq_sum fun g h => g * h = h * g
    _ = ((∑ g with g ∈ Z(G), #ₛ{ h : G | g * h = h * g })
        + ∑ g with g ∉ Z(G), #ₛ{ h : G | g * h = h * g }) / #ₜG ^ 2 := by
        rw [Finset.sum_filter_add_sum_filter_not]
    _ ≤ ((∑ g with g ∈ Z(G), #ₜG)
        + ∑ g with g ∉ Z(G), #ₛ{ h : G | g * h = h * g }) / #ₜG ^ 2 := by
        gcongr 3
        unfold typeQCard setQCard
        grw [ncard_le_ncard_univ]
        simp
    _ = (#ₜG * #ₜZ(G)
        + ∑ g with g ∉ Z(G), #ₛ{ h : G | g * h = h * g }) / #ₜG ^ 2 := by
        congr
        simp only [typeQCard]
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [Nat.card_eq_fintype_card, Fintype.card_subtype _]
        rw [mul_comm]
    _ = #ₜZ(G) / #ₜG
        + (∑ g with g ∉ Z(G), #ₛ{ h : G | g * h = h * g }) / #ₜG ^ 2 := by
        unfold typeQCard
        field_simp
    _ = centralFraction G
        + (∑ g with g ∉ Z(G), (#ₛ{ h : G | g * h = h * g }) / #ₜG) / #ₜG := by
        congr 1
        rw [pow_two, ← div_div, Finset.sum_div]
    _ = centralFraction G + (∑ g with g ∉ Z(G), centralizerFraction g) / #ₜG := by
        congr
        unfold centralizerFraction
        ext g
        field_simp
        congr 1
        ext h
        simp [Subgroup.mem_centralizer_singleton_iff]
        grind
    _ ≤ centralFraction G + (∑ g with g ∉ Z(G), 1 / 2) / #ₜG := by
        gcongr with g hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
        exact centralizerFraction_le_half hg
    _ = centralFraction G + (1 / 2) * (∑ g with g ∉ Z(G), 1) / #ₜG := by
        congr 1
        field_simp
        rw [Finset.sum_const]
        simp
        field_simp
    _ = centralFraction G + (1 / 2) * (#ₛ{ g : G | g ∉ Z(G) }) / #ₜG := by
        congr
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, setQCard, Nat.cast_inj]
        rw [Set.ncard_eq_toFinset_card]
        simp
    _ = centralFraction G
        + (1 / 2) * (#ₛ{ g : G | True } - #ₛ{ g : G | g ∈ Z(G) }) / #ₜG := by
        congr
        simp only [setQCard]
        have h1 : ({ g : G | g ∉ Z(G) } : Set G) = ({ g | g ∈ Z(G) } : Set G)ᶜ := by ext; simp
        have h2 : ({ g : G | True } : Set G) = Set.univ := by ext; simp
        rw [h1, Set.ncard_compl, h2, Set.ncard_univ]
        have hle : Set.ncard { g : G | g ∈ Z(G) } ≤ Nat.card G := by
          rw [← Set.ncard_univ G]
          exact Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
        exact Nat.cast_sub hle
    _ = centralFraction G + (1 / 2) * (#ₜG - #ₛ{ g : G | g ∈ Z(G) }) / #ₜG := by
        congr
        simp [typeQCard, setQCard]
    _ = centralFraction G + (1 / 2) * (1 - #ₛ{ g : G | g ∈ Z(G) } / #ₜG) := by
        field_simp
    _ = centralFraction G + (1 / 2) * (1 - centralFraction G) := by
        congr
    _ = 1 / 2 + centralFraction G / 2 := by
        field_simp
        ring
    _ ≤ 1 / 2 + 1 / 8 := by
        linarith [centralFraction_le_quarter h]
    _ = 5 / 8 := by norm_num

/-- **The 5/8 theorem**: the commuting probability of a nonabelian group is at most `5/8`. For
infinite groups, this follows from Mathlib's convention that `commProb` is `0`; the finite case is
Gustafson's theorem. -/
theorem commProb_le_five_eighths (G : Type*) [Group G] (h : ¬IsMulCommutative G) :
    commProb G ≤ 5 / 8 := by
  rcases finite_or_infinite G with hfinite | hinfinite
  · letI := hfinite
    exact commProb_le_five_eighths_of_finite G h
  · letI := hinfinite
    rw [commProb_eq_zero_of_infinite]
    norm_num

end FiveEighths
