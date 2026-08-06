/-
Copyright (c) 2026 Ricky Cipollini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ricky Cipollini
-/
import LeanPool.Erdos865.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The four sets `T₁,…,T₄` and their pairwise intersections

Supporting material for the folded additive lemma: the images `T₁,…,T₄` of `B` inside
`ZMod m`, their cardinalities, and the pairwise-intersection bounds culminating in the
four-set union bound `case2_bound`.
-/

open Finset

namespace Erdos865

/-! ### Generic helpers -/

/-
Inclusion–exclusion upper bound for four finite sets.
-/
theorem four_card_le {X : Type*} [DecidableEq X] (s1 s2 s3 s4 : Finset X) :
    s1.card + s2.card + s3.card + s4.card ≤
      (s1 ∪ s2 ∪ s3 ∪ s4).card +
        ((s1 ∩ s2).card + (s1 ∩ s3).card + (s1 ∩ s4).card +
          (s2 ∩ s3).card + (s2 ∩ s4).card + (s3 ∩ s4).card) := by
  have h1 := Finset.card_union_add_card_inter s1 ( s2 ∪ s3 ∪ s4 );
  have h2 := Finset.card_union_add_card_inter s2 ( s3 ∪ s4 )
  have h3 := Finset.card_union_add_card_inter s3 s4
  simp_all +decide [ Finset.inter_union_distrib_left ]
  linarith [ Finset.card_union_add_card_inter ( s1 ∩ s2 ) ( s1 ∩ s3 ∪ s1 ∩ s4 ),
    Finset.card_union_add_card_inter ( s1 ∩ s3 ) ( s1 ∩ s4 ),
    Finset.card_union_add_card_inter ( s2 ∩ s3 ) ( s2 ∩ s4 ) ]

/-
In `ZMod m` the equation `2 * x = c` has at most two solutions.
-/
theorem card_two_sol (m : ℕ) [NeZero m] (c : ZMod m) :
    (Finset.univ.filter (fun x : ZMod m => 2 * x = c)).card ≤ 2 := by
  by_contra! h_contra;
  -- Let S = univ.filter (fun x : ZMod m => 2*x = c). Show S ⊆ {a, b} where
  -- a = ((c.val/2 : ℕ) : ZMod m) and b = (((c.val+m)/2 : ℕ) : ZMod m);
  -- then card S ≤ card {a,b} ≤ 2 (Finset.card_le_card and Finset.card_le_two,
  -- or card_insert_le / card_pair).
  obtain ⟨a, b, hab⟩ : ∃ a b : ZMod m, ∀ x : ZMod m, 2 * x = c → x = a ∨ x = b := by
    use ((c.val / 2 : ℕ) : ZMod m), (((c.val + m) / 2 : ℕ) : ZMod m);
    intro x hx
    have h_eq : (2 * x.val : ℕ) % m = c.val % m := by
      simp +decide [ ← ZMod.natCast_eq_natCast_iff', hx ];
    -- Since $2 * x.val \equiv c.val \pmod{m}$, we have $2 * x.val = c.val + k * m$ for some
    -- integer $k$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * x.val = c.val + k * m := by
      exact ⟨ ( 2 * x.val ) / m,
        by linarith [ Nat.mod_add_div ( 2 * x.val ) m,
          Nat.mod_eq_of_lt ( show c.val < m from ZMod.val_lt c ) ] ⟩;
    rcases k with ( _ | _ | k ) <;> norm_num at *;
    · norm_num [ ← hk, mul_comm ];
    · norm_num [ ← hk, Nat.add_div ];
    · nlinarith [ x.val_lt, c.val_lt ];
  exact h_contra.not_ge ( le_trans ( Finset.card_le_card
    ( show Finset.filter ( fun x : ZMod m => 2 * x = c ) Finset.univ ⊆ { a, b }
      by intros x hx; aesop ) ) ( Finset.card_insert_le _ _ ) )

/-! ### The four sets `T₁,…,T₄` in `ZMod m` -/

/-- `T₁ = B` inside `ZMod m`. -/
def T1 (m : ℕ) (B : Finset ℕ) : Finset (ZMod m) := B.image (fun b : ℕ => (b : ZMod m))

/-- `T₂ = -B` inside `ZMod m`. -/
def T2 (m : ℕ) (B : Finset ℕ) : Finset (ZMod m) := B.image (fun b : ℕ => -(b : ZMod m))

/-- `T₃ = (B - α) \ {0}` inside `ZMod m`. -/
def T3 (m : ℕ) (B : Finset ℕ) (α : ℕ) : Finset (ZMod m) :=
  (B.image (fun b : ℕ => (b : ZMod m) - (α : ZMod m))).erase 0

/-- `T₄ = (β - B) \ {0}` inside `ZMod m`. -/
def T4 (m : ℕ) (B : Finset ℕ) (β : ℕ) : Finset (ZMod m) :=
  (B.image (fun b : ℕ => (β : ZMod m) - (b : ZMod m))).erase 0

/-
The cast `ℕ → ZMod m` is injective on `B` when `B ⊆ {1,…,m-1}`.
-/
theorem cast_injOn {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) :
    Set.InjOn (fun b : ℕ => (b : ZMod m)) (B : Set ℕ) := by
  intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy;
  simp_all +decide only [SetLike.mem_coe, ZMod.natCast_eq_natCast_iff'];
  exact fun h =>
    Nat.mod_eq_of_lt ( by linarith : x < m ) ▸ Nat.mod_eq_of_lt ( by linarith : y < m ) ▸ h

theorem card_T1 {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) : (T1 m B).card = B.card := by
  exact Finset.card_image_of_injOn (cast_injOn hB)

theorem card_T2 {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) : (T2 m B).card = B.card := by
  apply Finset.card_image_of_injOn;
  intro x hx y hy; have := cast_injOn hB; aesop;

theorem card_T3 {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {α : ℕ} (hα : α ∈ B) :
    (T3 m B α).card = B.card - 1 := by
  rw [ Erdos865.T3, Finset.card_erase_of_mem ];
  · rw [ Finset.card_image_of_injOn ];
    intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy;
    simp_all +decide only [SetLike.mem_coe, sub_eq_iff_eq_add, sub_add_cancel];
    exact fun h => Nat.mod_eq_of_lt ( by linarith : x < m ) ▸
      Nat.mod_eq_of_lt ( by linarith : y < m ) ▸
        by simpa [ ZMod.natCast_eq_natCast_iff' ] using h;
  · aesop

theorem card_T4 {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {β : ℕ} (hβ : β ∈ B) :
    (T4 m B β).card = B.card - 1 := by
  have h_inj : Set.InjOn (fun b : ℕ => (β : ZMod m) - (b : ZMod m)) (B : Set ℕ) := by
    intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy;
    simp_all +decide only [SetLike.mem_coe, sub_right_inj, ZMod.natCast_eq_natCast_iff'];
    exact fun h =>
      Nat.mod_eq_of_lt ( by linarith : x < m ) ▸ Nat.mod_eq_of_lt ( by linarith : y < m ) ▸ h;
  rw [Erdos865.T4,
    Finset.card_erase_of_mem (Finset.mem_image.mpr ⟨β, hβ, by simp⟩),
    Finset.card_image_of_injOn h_inj]

/-
None of the four sets contain `0`, so their union misses `0`.
-/
theorem union_card_le {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) (α β : ℕ) :
    haveI : NeZero m := ⟨by omega⟩
    (T1 m B ∪ T2 m B ∪ T3 m B α ∪ T4 m B β).card ≤ m - 1 := by
  have : NeZero m := ⟨by omega⟩
  have hsub : T1 m B ∪ T2 m B ∪ T3 m B α ∪ T4 m B β ⊆ Finset.univ.erase (0 : ZMod m) := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ x⟩
    simp only [Finset.mem_union] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · rw [T1, Finset.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨ha1, ha2⟩ := hB.1 a ha
      simpa [ZMod.natCast_eq_zero_iff] using Nat.not_dvd_of_pos_of_lt (by omega) ha2
    · rw [T2, Finset.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨ha1, ha2⟩ := hB.1 a ha
      simpa [neg_eq_zero, ZMod.natCast_eq_zero_iff] using Nat.not_dvd_of_pos_of_lt (by omega) ha2
    · rw [T3] at hx; exact (Finset.mem_erase.mp hx).1
    · rw [T4] at hx; exact (Finset.mem_erase.mp hx).1
  calc (T1 m B ∪ T2 m B ∪ T3 m B α ∪ T4 m B β).card
      ≤ (Finset.univ.erase (0 : ZMod m)).card := Finset.card_le_card hsub
    _ = m - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-! ### The pairwise intersection bounds -/

theorem inter_T1_T2_le {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) :
    (T1 m B ∩ T2 m B).card ≤ 1 := by
  -- Take an arbitrary element z ∈ T1 m B ∩ T2 m B.
  have h_eq : ∀ z ∈ T1 m B ∩ T2 m B, ∃ b ∈ B, z = (b : ZMod m) ∧ 2 * b = m := by
    intro z hz
    obtain ⟨b, hbB, hbz⟩ : ∃ b ∈ B, (b : ZMod m) = z := by
      unfold T1 at hz; aesop;
    obtain ⟨b', hb'B, hb'z⟩ : ∃ b' ∈ B, -(b' : ZMod m) = z := by
      unfold T2 at hz; aesop;
    have h_eq : m ∣ (b + b') := by
      simp_all +decide only [mem_inter, ← ZMod.natCast_eq_zero_iff, Nat.cast_add];
      rw [ ← hb'z, neg_add_cancel ];
    have h_eq : b + b' = m := by
      have := hB.1 b hbB; have := hB.1 b' hb'B; obtain ⟨ k, hk ⟩ := h_eq;
      nlinarith [ show k = 1 by nlinarith ];
    have := hB.2 b hbB b' hb'B; simp_all +decide [ two_mul ] ;
    grind;
  exact Finset.card_le_one.mpr fun x hx y hy => by
    obtain ⟨ b₁, hb₁, rfl, hb₁' ⟩ := h_eq x hx; obtain ⟨ b₂, hb₂, rfl, hb₂' ⟩ := h_eq y hy; aesop;

theorem inter_T1_T2_odd {m : ℕ} (hodd : ¬ 2 ∣ m) {B : Finset ℕ} (hB : FoldedOK m B) :
    T1 m B ∩ T2 m B = ∅ := by
  simp +decide only [Nat.two_dvd_ne_zero, T1, T2, Finset.ext_iff, mem_inter, mem_image,
    notMem_empty, iff_false, not_and, not_exists, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at *;
  intro a ha b hb; rw [ neg_eq_iff_add_eq_zero ] ; have := hB.1 a ha; have := hB.1 b hb;
  simp_all +decide only [ne_eq];
  by_contra h_contra
  have h_div : m ∣ (a + b) := by
    simp_all +decide [ ← ZMod.natCast_eq_zero_iff, add_comm ]
  have h_eq : a + b = m := by
    obtain ⟨ k, hk ⟩ := h_div; nlinarith [ show k = 1 by nlinarith ] ;
  have h_contra' : a ≠ b := by
    omega
  have h_contra'' : a + b ≠ m := by
    exact hB.2 a ha b hb h_contra' |>.1
  contradiction

theorem inter_T1_T3_le {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {α : ℕ} (hα : α ∈ B) :
    (T1 m B ∩ T3 m B α).card ≤ 1 := by
  by_contra h_contra;
  obtain ⟨x, hx⟩ : ∃ x ∈ T1 m B ∩ T3 m B α, x ≠ (α : ZMod m) := by
    exact Exists.elim ( Finset.exists_mem_ne ( lt_of_not_ge h_contra ) _ )
      fun x hx => ⟨ x, hx.1, hx.2 ⟩;
  obtain ⟨b, hb, hb_eq⟩ : ∃ b ∈ B, x = (b : ZMod m) := by
    unfold T1 at hx; aesop;
  obtain ⟨c, hc, hc_eq⟩ : ∃ c ∈ B, x = (c : ZMod m) - (α : ZMod m) ∧ c ≠ α := by
    unfold T3 at hx; aesop;
  have h_mod : (b + α) % m = c % m := by
    simp_all +decide only [not_le, mem_inter, ne_eq, ← ZMod.natCast_eq_natCast_iff', Nat.cast_add];
    linear_combination' -hb_eq;
  have := hB.2 b hb α hα; simp_all +decide only [not_le, mem_inter, ne_eq] ;
  exact this ( by aesop ) |>.2
    ( by simpa [ Nat.mod_eq_of_lt ( show c < m from hB.1 c hc |>.2 ) ] using hc )

theorem inter_T2_T3_le {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {α : ℕ} (hα : α ∈ B)
    (hmin : ∀ x ∈ B, α ≤ x) : (T2 m B ∩ T3 m B α).card ≤ 1 := by
  -- Since $z \in T2 \cap T3$, we have $z = -(u : ZMod m)$ and $u \in B$, and
  -- $z = (b : ZMod m) - (α : ZMod m)$ and $b \in B$. Thus,
  have h_eq : ∀ z ∈ T2 m B ∩ T3 m B α, ∃ u ∈ B, z = -(u : ZMod m) ∧ ∃ b ∈ B,
      z = (b : ZMod m) - (α : ZMod m) ∧ u = b ∧ 2 * u = α + m := by
    intro z hz
    obtain ⟨u, huB, hu⟩ : ∃ u ∈ B, z = -(u : ZMod m) := by
      unfold T2 at hz; aesop;
    obtain ⟨b, hbB, hb⟩ : ∃ b ∈ B, z = (b : ZMod m) - (α : ZMod m) := by
      grind +locals
    have h_eq : (u + b : ℕ) % m = α % m := by
      simp_all +decide only [mem_inter, ← ZMod.natCast_eq_natCast_iff', Nat.cast_add];
      linear_combination' hu
    have h_eq' : (u + b : ℕ) = α ∨ (u + b : ℕ) = α + m := by
      have h_eq' : (u + b : ℕ) < 2 * m := by
        linarith [ hB.1 u huB, hB.1 b hbB ];
      have h_eq' : (u + b : ℕ) = α + m * ((u + b) / m) := by
        linarith [ Nat.mod_add_div ( u + b ) m,
          Nat.mod_eq_of_lt ( show α < m from hB.1 α hα |>.2 ) ];
      have : ( u + b ) / m ≤ 1 := Nat.le_of_lt_succ ( Nat.div_lt_of_lt_mul <| by linarith )
      interval_cases ( u + b ) / m <;>
        simp +decide only [mul_zero, add_zero, mul_one] at h_eq' ⊢;
      · exact Or.inl h_eq';
      · exact Or.inr h_eq'
    have h_eq'' : u = b := by
      cases h_eq' <;> have := hB.2 u huB b hbB <;> simp_all +decide;
      · grind +qlia;
      · have := hB.1 α hα; simp_all +decide [ Nat.mod_eq_of_lt ] ;
    have h_eq''' : 2 * u = α + m := by
      cases h_eq' <;> simp_all +decide [ two_mul ];
      linarith [ hmin _ hbB, show α > 0 from hB.1 _ hα |>.1 ]
    use u, huB, hu, b, hbB, hb, h_eq'', h_eq''';
  -- Since $2u = α + m$, and $u$ is uniquely determined, the set $T2 \cap T3$ can contain at
  -- most one element.
  have h_unique : ∀ z ∈ T2 m B ∩ T3 m B α, ∀ z' ∈ T2 m B ∩ T3 m B α, z = z' := by
    grind;
  exact Finset.card_le_one.mpr h_unique

theorem inter_T2_T4_le {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {β : ℕ} (hβ : β ∈ B) :
    (T2 m B ∩ T4 m B β).card ≤ 1 := by
  rw [ Finset.card_le_one_iff ];
  intros a b ha hb
  have h_eq : ∀ z ∈ T2 m B ∩ T4 m B β, z = -(β : ZMod m) := by
    intros z hz
    obtain ⟨u, hu⟩ : ∃ u ∈ B, z = -(u : ZMod m) := by
      unfold T2 at hz; aesop;
    obtain ⟨b, hb⟩ : ∃ b ∈ B, z = (β : ZMod m) - (b : ZMod m) := by
      unfold T4 at hz; aesop;
    have h_eq : (b : ZMod m) = (β : ZMod m) + (u : ZMod m) := by
      grind;
    have h_eq_mod : (β + u) % m = b % m := by
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
    have h_eq_mod : (β + u) % m ∈ B := by
      have := hB.1 b hb.1; simp_all +decide [ Nat.mod_eq_of_lt ] ;
    have := hB.2 β hβ u hu.1; simp_all +decide ;
  rw [ h_eq a ha, h_eq b hb ]

theorem inter_T1_T4_le {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) {β : ℕ}
    (hβ : β ∈ B) : (T1 m B ∩ T4 m B β).card ≤ 2 := by
  have := @card_two_sol m ⟨ by omega ⟩ ( β : ZMod m );
  refine le_trans ( Finset.card_le_card ?_ ) this;
  intro x hx; simp_all +decide [ T1, T4 ] ;
  obtain ⟨ ⟨ a, ha, rfl ⟩, hx, ⟨ b, hb, hx' ⟩ ⟩ := hx; simp_all +decide [ sub_eq_iff_eq_add ] ;
  by_cases hab : a = b <;> simp_all +decide [ two_mul ];
  have := hB.2 a ha b hb hab; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ] ;
  have := hB.1 β hβ; simp_all +decide [ ZMod.natCast_eq_zero_iff ] ;
  have := Nat.mod_eq_of_lt this.2; simp_all +decide [ ← ZMod.val_natCast ] ;

theorem inter_T3_T4_le {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {α β : ℕ}
    (hα : α ∈ B) (hβ : β ∈ B) (hαβ : α < β) (hmin : ∀ x ∈ B, α ≤ x)
    (hmin2 : ∀ x ∈ B, x ≠ α → β ≤ x) (hsum : α + β < m)
    (hnc : α + β ∉ collisions m B) : (T3 m B α ∩ T4 m B β).card ≤ 2 := by
  have h_inter_T3_T4_le : ∀ z ∈ T3 m B α ∩ T4 m B β, ∀ b ∈ B, ∀ b' ∈ B,
      z = (b : ZMod m) - (α : ZMod m) ∧ z = (β : ZMod m) - (b' : ZMod m) →
        b = β ∨ ∃ c ∈ B, 2 * c = α + β + m ∧ z = (c : ZMod m) - (α : ZMod m) := by
    intros z hz b hb b' hb' h_eq
    have h_sum : (b + b') % m = (α + β) % m := by
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
      grind
    have h_cases : b + b' = α + β ∨ b + b' = α + β + m := by
      obtain ⟨ k, hk ⟩ := Nat.modEq_iff_dvd.mp h_sum.symm;
      rcases lt_trichotomy k 0 with hk' | rfl | hk' <;> norm_num at hk ⊢ <;>
        try (left; nlinarith [ hB.1 b hb, hB.1 b' hb' ]);
      exact Or.inr ( by nlinarith [ show k = 1 by nlinarith [ hB.1 b hb, hB.1 b' hb' ] ] )
    obtain h_case1 | h_case2 := h_cases
    · generalize_proofs at *
      by_cases hb_eq_α : b = α <;> by_cases hb'_eq_β : b' = β <;> simp_all +decide [ add_comm ]
      · unfold T3 T4 at hz; aesop
      · omega
      · grind +splitImp
    · by_cases hbb' : b = b' <;>
        simp_all +decide only [ne_eq, collisions, mem_inter, not_and, sub_left_inj,
          Nat.add_mod_right]
      · exact Or.inr ⟨ b', hb', by linarith, rfl ⟩
      · contrapose! hnc
        simp_all +decide only [ne_eq, lowSums, mem_image, mem_filter, mem_product, Prod.exists,
          highSums]
        exact ⟨ ⟨ α, β, ⟨ ⟨ hα, hβ ⟩, by linarith, by linarith ⟩, rfl ⟩,
          ⟨ b, b', ⟨ ⟨ hb, hb' ⟩, hbb', by linarith ⟩, Nat.sub_eq_of_eq_add <| by linarith ⟩ ⟩
  have h_inter_T3_T4_le : ∀ z ∈ T3 m B α ∩ T4 m B β, z = (β : ZMod m) - (α : ZMod m) ∨
      ∃ c ∈ B, 2 * c = α + β + m ∧ z = (c : ZMod m) - (α : ZMod m) := by
    grind +locals;
  have h_inter_T3_T4_le : ∀ c1 c2 : ℕ, c1 ∈ B → c2 ∈ B → 2 * c1 = α + β + m →
      2 * c2 = α + β + m → c1 = c2 := by
    intros c1 c2 hc1 hc2 hc1_eq hc2_eq
    linarith;
  have h_inter_T3_T4_le : ∀ z1 z2 : ZMod m, z1 ∈ T3 m B α ∩ T4 m B β →
      z2 ∈ T3 m B α ∩ T4 m B β →
        z1 = (β : ZMod m) - (α : ZMod m) ∨ z2 = (β : ZMod m) - (α : ZMod m) ∨ z1 = z2 := by
    grind;
  contrapose! h_inter_T3_T4_le;
  obtain ⟨ z1, hz1, z2, hz2, hne ⟩ := Finset.two_lt_card.mp h_inter_T3_T4_le;
  grind

/-! ### The Case 2 bound -/

/-
The four-set union bound of Case 2 of the folded additive lemma.
-/
theorem case2_bound {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) {α β : ℕ}
    (hα : α ∈ B) (hβ : β ∈ B) (hαβ : α < β) (hmin : ∀ x ∈ B, α ≤ x)
    (hmin2 : ∀ x ∈ B, x ≠ α → β ≤ x) (hsum : α + β < m)
    (hnc : α + β ∉ collisions m B) : 4 * B.card ≤ m + 8 := by
  by_cases h_even : 2 ∣ m
  · have := ( four_card_le ( T1 m B ) ( T2 m B ) ( T3 m B α ) ( T4 m B β ) )
    rw [ card_T1 hB, card_T2 hB, card_T3 hB hα, card_T4 hB hβ ] at this
    have := union_card_le hm hB α β
    have := inter_T1_T2_le hB
    have := inter_T1_T3_le hB hα
    have := inter_T1_T4_le hm hB hβ
    have := inter_T2_T3_le hB hα hmin
    have := inter_T2_T4_le hB hβ
    have := inter_T3_T4_le hB hα hβ hαβ hmin hmin2 hsum hnc
    omega
  · have h_union_card : (T1 m B ∪ T2 m B ∪ T3 m B α ∪ T4 m B β).card ≤ m - 1 := by
      convert union_card_le hm hB α β using 1
    have h_four_card_le : (T1 m B).card + (T2 m B).card + (T3 m B α).card + (T4 m B β).card ≤
        (T1 m B ∪ T2 m B ∪ T3 m B α ∪ T4 m B β).card +
          ((T1 m B ∩ T2 m B).card + (T1 m B ∩ T3 m B α).card + (T1 m B ∩ T4 m B β).card +
            (T2 m B ∩ T3 m B α).card + (T2 m B ∩ T4 m B β).card + (T3 m B α ∩ T4 m B β).card) := by
      convert four_card_le ( T1 m B ) ( T2 m B ) ( T3 m B α ) ( T4 m B β ) using 1
    have := inter_T1_T3_le hB hα
    have := inter_T2_T3_le hB hα hmin
    have := inter_T2_T4_le hB hβ
    have := inter_T1_T4_le hm hB hβ
    have := inter_T3_T4_le hB hα hβ hαβ hmin hmin2 hsum hnc
    simp_all +decide [ card_T1, card_T2, card_T3, card_T4 ]
    have := inter_T1_T2_odd ( show ¬2 ∣ m from by omega ) hB
    simp_all +decide [ Finset.ext_iff ]
    omega

end Erdos865
