/-
Copyright (c) 2026 Ricky Cipollini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ricky Cipollini
-/
import LeanPool.Erdos865.Folding

/-!
# The even-`N` upper bound (Erdős 865, §4)

Strong induction on `N` proving `even_bound`: every triple-free `A ⊆ [1, 2e]` satisfies the
`5/8` counting bound, split into the cases `even_bound_case1` and `even_bound_case2`.
-/

open Finset

namespace Erdos865

/-
Counting bound: every element of `A ⊆ [1,N]` is counted by `X`, by `Y`, is one of the
two endpoints `h, 2h`, or lies in the tail `(2h, N]`.
-/
theorem card_A_bound {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Finset.Icc 1 N) (h : ℕ) :
    A.card ≤ (Xset A h).card + (Yset A N h).card + 2 + (N - 2 * h) := by
  -- Let's show that $A$ is a subset of
  -- $Xset A h ∪ (Yset A N h).image (fun r => h + r) ∪ {h, 2*h} ∪ Finset.Icc (2*h + 1) N$.
  have h_subset : A ⊆ Xset A h ∪ (Yset A N h).image (fun r => h + r) ∪ {h, 2 * h} ∪
      Finset.Icc (2 * h + 1) N := by
    intro a ha; by_cases ha1 : a < h <;> by_cases ha2 : a = h <;> by_cases ha3 : a = 2 * h <;>
      simp_all +decide only [subset_iff, mem_Icc, lt_self_iff_false, not_lt, not_false_eq_true,
        mem_singleton, insert_eq_of_mem, union_insert, union_assoc, union_singleton, insert_union,
        mem_insert, mem_union, mem_image, Nat.add_eq_left, exists_eq_right, add_le_iff_nonpos_right,
        Order.add_one_le_iff, and_true, or_false, false_or, true_or, or_true];
    · exact Or.inl <|
        Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ by linarith [ hsub ha ], ha1 ⟩, ha ⟩;
    · by_cases ha4 : a < 2 * h <;>
        simp_all +decide only [not_lt, Xset, mem_filter, mem_Ico, true_and, and_true, Yset];
      · exact Or.inr <| Or.inl
          ⟨ a - h, ⟨ ⟨ Nat.sub_pos_of_lt <| lt_of_le_of_ne ha1 <| Ne.symm ha2, by omega ⟩,
            by linarith [ hsub ha, Nat.sub_add_cancel ha1 ], by convert ha using 1; omega ⟩,
            by omega ⟩;
      · exact Or.inr <| Or.inr <| lt_of_le_of_ne ha4 <| Ne.symm ha3;
  refine le_trans ( Finset.card_le_card h_subset ) ?_;
  refine le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( le_trans ( Finset.card_union_le _ _ )
    ( add_le_add ( le_trans ( Finset.card_union_le _ _ ) ( add_le_add
      ( Finset.card_le_card ( Finset.Subset.refl _ ) ) ( Finset.card_image_le ) ) )
      ( Finset.card_insert_le _ _ ) ) ) ( by simp +arith +decide [ Nat.card_Icc ] ) )

/-
The open interval `(p, q)` contains no element of `A`.
-/
theorem gap_empty {A : Finset ℕ} {H p q : ℕ} (_hqlo : H ≤ q)
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) :
    ∀ a ∈ A, ¬ (p < a ∧ a < q) := by
  grind +qlia

/-
Case 1 interval `I = (max(p, N-h), h)` is contained in `E \ C(B_h)` for `h = q`.
-/
theorem case1_I_sub {A : Finset ℕ} {H p q : ℕ} (_hqlo : H ≤ q)
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) :
    Finset.Ico (max p (2 * H - q) + 1) q ⊆
      Eset A (2 * H) q \ collisions q (Bset A (2 * H) q) := by
  intro x hx;
  simp_all +decide only [mem_Ico, Order.add_one_le_iff, sup_lt_iff, Eset, Bset, mem_sdiff, and_true,
    mem_union, not_or];
  refine ⟨ ⟨ by linarith, ?_, ?_ ⟩, ?_ ⟩ <;>
    simp_all +decide only [Xset, Yset, mem_filter, mem_Ico, and_true, not_and, collisions,
      mem_inter];
  · grind;
  · grind;
  · intro hx₁ hx₂; simp_all +decide [ lowSums, highSums ] ;
    omega

/-
**Case 1** (`s ≤ 4e`): folding around `h = q`.
-/
theorem even_bound_case1 {H p q : ℕ} {A : Finset ℕ} (hsub : A ⊆ Finset.Icc 1 (2 * H))
    (hA : IsTripleFree A) (hq : q ∈ A) (hqlo : H ≤ q) (hqhi : q ≤ 2 * H)
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (_hp : p ∈ A) (_hplo : 1 ≤ p) (hphi : p ≤ H)
    (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) (hcase : q - H ≤ 4 * (H - p)) :
    4 * A.card ≤ 5 * H + 24 := by
  have := @folding_lemma A ( 2 * H ) q ?_ ?_ <;>
    simp_all +decide only [tsub_le_iff_right, ge_iff_le];
  have hIle := Finset.card_le_card
    ( case1_I_sub hqlo hqmin hpmax :
      Finset.Ico ( Max.max p ( 2 * H - q ) + 1 ) q ⊆
        Eset A ( 2 * H ) q \ collisions q ( Bset A ( 2 * H ) q ) );
  simp_all +decide [ Nat.card_Ico ];
  have hcount := card_A_bound hsub q; simp_all +decide ;
  omega

/-
In case 2 (`h = p`), the folded coordinate set avoids `[1, q-p-1]`, since for
`1 ≤ r < q - p` the partner `p + r` lies in the empty gap `(p, q)`.
-/
theorem case2_Bset_disjoint {A : Finset ℕ} {H p q : ℕ}
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) :
    Bset A (2 * H) p ∩ Finset.Ico 1 (q - p) = ∅ := by
  simp +decide [ Bset, Yset ];
  grind +splitIndPred

/-
Case 2 interval `I = [1, t] \ A` (with `t = q - p - 1`) is contained in `E \ C(B_p)`,
provided `q - p ≤ p` (so the interval sits below the pivot).
-/
theorem case2_I_sub {A : Finset ℕ} {H p q : ℕ} (hple : q - p ≤ p)
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) :
    Finset.Ico 1 (q - p) \ A ⊆ Eset A (2 * H) p \ collisions p (Bset A (2 * H) p) := by
  intro x hx; simp_all +decide only [tsub_le_iff_right, mem_sdiff, mem_Ico] ;
  constructor;
  · simp_all +decide [ Eset, Xset, Yset ];
    grind +splitImp;
  · intro hx';
    obtain ⟨ y, hy, z, hz, hyz, rfl ⟩ := Finset.mem_image.mp ( Finset.mem_inter.mp hx' |>.1 );
    simp_all +decide [ Bset, Xset, Yset ];
    grind

/-- A subset of a triple-free set is triple-free. -/
theorem tripleFree_subset {A B : Finset ℕ} (hA : IsTripleFree A) (h : B ⊆ A) :
    IsTripleFree B := by
  intro ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hab', hac', hbc'⟩
  exact hA ⟨a, h ha, b, h hb, c, h hc, hab, hac, hbc, h hab', h hac', h hbc'⟩

/-
**Case 2** (`s > 4e`): folding around `h = p`, using the induction hypothesis on
`A ∩ [1, q-p-1]`.
-/
theorem even_bound_case2 {H p q : ℕ} {A : Finset ℕ} (hsub : A ⊆ Finset.Icc 1 (2 * H))
    (hA : IsTripleFree A) (hqlo : H ≤ q) (hqhi : q ≤ 2 * H)
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (hp : p ∈ A) (hplo : 1 ≤ p) (hphi : p ≤ H)
    (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) (hcase : 4 * (H - p) < q - H)
    (IH : ∀ H' (A' : Finset ℕ), H' < H → A' ⊆ Finset.Icc 1 (2 * H') → IsTripleFree A' →
      4 * A'.card ≤ 5 * H' + 24) :
    4 * A.card ≤ 5 * H + 24 := by
  by_cases hq_p : p < q - p;
  · have hAsub : A ⊆ Finset.Icc 1 p ∪ Finset.Icc q (2 * H) := by
      grind;
    have := Finset.card_mono hAsub; simp_all +decide [ Finset.card_union ] ;
    omega;
  · -- Apply the folding_lemma to get the inequality involving the cardinalities of Xset, Yset,
    -- and Eset.
    have h_fold : 4 * ((Xset A p).card + (Yset A (2 * H) p).card) +
        4 * (Eset A (2 * H) p \ collisions p (Bset A (2 * H) p)).card ≤ 5 * p + 4 := by
      apply folding_lemma hA hp;
    have h_I_sub : (Finset.Ico 1 (q - p) \ A) ⊆
        Eset A (2 * H) p \ collisions p (Bset A (2 * H) p) := by
      apply case2_I_sub (by
      omega) hqmin hpmax;
    have h_A0 : 4 * (A ∩ Finset.Ico 1 (q - p)).card ≤ 5 * ((q - p) / 2) + 24 := by
      apply IH ((q - p) / 2) (A ∩ Finset.Ico 1 (q - p));
      · omega;
      · grind;
      · exact tripleFree_subset hA ( Finset.inter_subset_left );
    have h_card_A : A.card ≤ (Xset A p).card + (Yset A (2 * H) p).card + 2 + (2 * H - 2 * p) := by
      apply card_A_bound hsub p;
    have h_card_Ico : (Finset.Ico 1 (q - p)).card =
        (Finset.Ico 1 (q - p) \ A).card + (A ∩ Finset.Ico 1 (q - p)).card := by
      grind;
    have := Finset.card_le_card h_I_sub; simp_all +decide ;
    omega

/-
The even-`N` upper bound: every triple-free `A ⊆ [1, 2H]` has `4|A| ≤ 5H + 24`,
i.e. `|A| ≤ 5H/4 + 6`. Proved by strong induction on `H`.
-/
theorem even_bound (H : ℕ) (A : Finset ℕ) (hsub : A ⊆ Finset.Icc 1 (2 * H))
    (hA : IsTripleFree A) : 4 * A.card ≤ 5 * H + 24 := by
  induction H using Nat.strong_induction_on generalizing A
  rename_i H ih
  by_cases h1 : (A ∩ Finset.Icc H (2 * H)).Nonempty;
  · by_cases h2 : (A ∩ Finset.Icc 1 H).Nonempty;
    · -- Let $q = \min(A \cap [H, 2H])$ and $p = \max(A \cap [1, H])$.
      obtain ⟨q, hq⟩ : ∃ q ∈ A, H ≤ q ∧ q ≤ 2 * H ∧ ∀ a ∈ A, H ≤ a → q ≤ a := by
        exact ⟨ Nat.find h1,
          Nat.find_spec h1 |> fun x => Finset.mem_of_mem_inter_left x,
          Nat.find_spec h1 |> fun x => Finset.mem_Icc.mp ( Finset.mem_inter.mp x |>.2 ) |>.1,
          Nat.find_spec h1 |> fun x => Finset.mem_Icc.mp ( Finset.mem_inter.mp x |>.2 ) |>.2,
          fun a ha ha' => Nat.find_min' h1 <|
            Finset.mem_inter.mpr
              ⟨ ha, Finset.mem_Icc.mpr ⟨ ha', by linarith [ Finset.mem_Icc.mp ( hsub ha ) ] ⟩ ⟩ ⟩
      obtain ⟨p, hp⟩ : ∃ p ∈ A, 1 ≤ p ∧ p ≤ H ∧ ∀ a ∈ A, a ≤ H → a ≤ p := by
        obtain ⟨p, hp⟩ : ∃ p ∈ A ∩ Finset.Icc 1 H, ∀ a ∈ A ∩ Finset.Icc 1 H, a ≤ p := by
          exact ⟨ Finset.max' _ h2, Finset.max'_mem _ h2, fun a ha => Finset.le_max' _ _ ha ⟩;
        exact ⟨ p, Finset.mem_of_mem_inter_left hp.1,
          Finset.mem_Icc.mp ( Finset.mem_inter.mp hp.1 |>.2 ) |>.1,
          Finset.mem_Icc.mp ( Finset.mem_inter.mp hp.1 |>.2 ) |>.2,
          fun a ha ha' => hp.2 a
            ( Finset.mem_inter.mpr
              ⟨ ha, Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( hsub ha ) |>.1, ha' ⟩ ⟩ ) ⟩;
      by_cases hcase : q - H ≤ 4 * (H - p);
      · apply even_bound_case1 hsub hA hq.left hq.right.left hq.right.right.left
          hq.right.right.right hp.left hp.right.left hp.right.right.left hp.right.right.right hcase;
      · apply even_bound_case2 hsub hA hq.right.left hq.right.right.left hq.right.right.right
          hp.left hp.right.left hp.right.right.left hp.right.right.right (by omega)
          (fun H' A' h1 h2 h3 => ih H' h1 A' h2 h3);
    · simp_all +decide only [not_nonempty_iff_eq_empty, Finset.ext_iff, mem_inter, mem_Icc,
        notMem_empty, iff_false, not_and, not_le];
      have := Finset.card_le_card ( show A ⊆ Finset.Icc ( H + 1 ) ( 2 * H ) from fun x hx =>
        Finset.mem_Icc.mpr ⟨ by linarith [ h2 x hx ( Finset.mem_Icc.mp ( hsub hx ) |>.1 ) ],
          by linarith [ Finset.mem_Icc.mp ( hsub hx ) |>.2 ] ⟩ );
      simp_all +arith +decide;
      omega;
  · rcases H with ( _ | H ) <;>
      simp_all +decide only [not_lt_zero, not_isEmpty_of_nonempty, IsEmpty.forall_iff, implies_true,
        mul_zero, Order.lt_one_iff, Icc_eq_empty_of_lt, subset_empty, Finset.Nonempty, Icc_self,
        notMem_empty, not_false_eq_true, inter_singleton_of_notMem, exists_const, card_empty,
        zero_add, zero_le, Order.lt_add_one_iff, mem_inter, mem_Icc, Order.add_one_le_iff,
        not_exists, not_and, not_le];
    exact le_trans ( Nat.mul_le_mul_left _ ( Finset.card_le_card
      ( show A ⊆ Finset.Icc 1 ( H + 1 ) from fun x hx => Finset.mem_Icc.mpr
        ⟨ Finset.mem_Icc.mp ( hsub hx ) |>.1,
          Nat.le_of_not_lt fun hx' =>
            by linarith [ Finset.mem_Icc.mp ( hsub hx ) |>.2, h1 x hx ( by linarith ) ] ⟩ ) ) )
      ( by simp +arith +decide )

end Erdos865
