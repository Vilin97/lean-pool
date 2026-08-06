/-
Copyright (c) 2026 Ricky Cipollini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ricky Cipollini
-/
import LeanPool.Erdos865.FoldedMain

/-!
# The folding lemma (Erdős 865, §3)

Folds a triple-free set `A ⊆ [1,N]` onto a `FoldedOK` set `B_h` and controls the
collisions via the exceptional set, giving the folding lemma `folding_lemma`.
-/

open Finset

namespace Erdos865

/-
For a triple-free set `A` with pivot `h ∈ A` and `h ≥ 2`, the folded coordinate set
`B_h` satisfies the hypothesis of the folded additive lemma modulo `h`.
-/
theorem foldedOK_Bset {A : Finset ℕ} {N h : ℕ} (hA : IsTripleFree A) (hh : h ∈ A)
    (_hh2 : 2 ≤ h) : FoldedOK h (Bset A N h) := by
  constructor;
  · exact fun x hx => by unfold Bset at hx; unfold Xset at hx; unfold Yset at hx; aesop;
  · intro x hx y hy hxy;
    refine ⟨ ?_, ?_ ⟩ <;> contrapose! hxy <;>
      simp_all +decide only [Bset, Xset, Yset, mem_inter, mem_filter, mem_Ico];
    · unfold IsTripleFree at hA; simp_all +decide [ HasTriple ] ;
      grind +ring;
    · -- If $x + y \geq h$, then $(x + y) \% h = x + y - h$, which is in $A$.
      by_cases hxy_ge_h : x + y ≥ h;
      · have hxy_mod : (x + y) % h = x + y - h := by
          rw [ Nat.mod_eq_sub_mod hxy_ge_h ];
          rw [ Nat.mod_eq_of_lt ( by omega ) ];
        contrapose! hA;
        simp_all +decide only [add_tsub_cancel_of_le, ge_iff_le, ne_eq, IsTripleFree, not_not];
        use x, hx.1.2, y, hy.1.2, h, hh;
        grind;
      · simp_all +decide [ Nat.mod_eq_of_lt ( not_le.mp hxy_ge_h ) ];
        unfold IsTripleFree at hA; simp_all +decide [ HasTriple ] ;
        grind +ring

/-
Collisions of `B_h` land in the "excluded" set `E`.
-/
theorem collisions_subset_Eset {A : Finset ℕ} {N h : ℕ} (hA : IsTripleFree A) (hh : h ∈ A) :
    collisions h (Bset A N h) ⊆ Eset A N h := by
  intro r hr;
  refine Finset.mem_sdiff.mpr ⟨ ?_, ?_ ⟩;
  · unfold collisions at hr;
    unfold lowSums highSums at hr;
    grind;
  · simp_all +decide only [collisions, lowSums, ne_eq, highSums, mem_inter, mem_image, mem_filter,
      mem_product, Prod.exists, Xset, Yset, mem_union, mem_Ico, not_or, not_and, and_imp];
    constructor <;> intros <;> simp_all +decide only [Bset, mem_inter];
    · obtain ⟨ ⟨ a, b, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, hb₁, hb₂ ⟩, hab, hlt ⟩, rfl ⟩,
        c, d, ⟨ ⟨ ⟨ hc₁, hc₂ ⟩, hd₁, hd₂ ⟩, hcd, hlt' ⟩, hcd' ⟩ := hr;
      contrapose! hA;
      unfold IsTripleFree;
      simp_all +decide only [Xset, mem_filter, mem_Ico, Yset, and_self, true_and, not_not];
      exact ⟨ a, ha₁.2, b, hb₁.2, h, hh, by omega, by omega, by omega, by ring_nf at *; aesop ⟩;
    · obtain ⟨ a, b, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, ⟨ hb₁, hb₂ ⟩ ⟩, hab, hlt ⟩, rfl ⟩ := hr.2;
      contrapose! hA;
      unfold IsTripleFree;
      simp_all +decide only [Xset, mem_filter, mem_Ico, Yset, and_self, true_and, not_not];
      use a, ha₁.2, b, hb₁.2, h, hh;
      grind

/-
The elementary counting identity `|X| + |Y| + |E| = (h-1) + |B_h|`.
-/
theorem card_XY_E (A : Finset ℕ) (N h : ℕ) :
    (Xset A h).card + (Yset A N h).card + (Eset A N h).card = (h - 1) + (Bset A N h).card := by
  rw [ Eset, Finset.card_sdiff ];
  rw [ ← Finset.card_union_add_card_inter, Bset ];
  rw [ show ( Xset A h ∪ Yset A N h ) ∩ Ico 1 h = Xset A h ∪ Yset A N h from ?_ ];
  · rw [ add_right_comm, Nat.add_sub_of_le ];
    · simp +arith +decide;
    · exact Finset.card_le_card
        ( Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) );
  · exact Finset.inter_eq_left.mpr
      ( Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) )

/-
**Folding lemma.** For a triple-free `A` and pivot `h ∈ A`,
`4(|X|+|Y|) + 4|E \ C(B_h)| ≤ 5h + 4`, i.e. `|X|+|Y| ≤ 5h/4 - |E \ C(B_h)| + 1`.
-/
theorem folding_lemma {A : Finset ℕ} {N h : ℕ} (hA : IsTripleFree A) (hh : h ∈ A) :
    4 * ((Xset A h).card + (Yset A N h).card)
      + 4 * (Eset A N h \ collisions h (Bset A N h)).card ≤ 5 * h + 4 := by
  by_cases h_ge_2 : 2 ≤ h;
  · -- By the folding lemma, we have $4 * |B_h| \leq 4 * |C(B_h)| + h + 8$.
    have h_folding : 4 * (Bset A N h).card ≤ 4 * (collisions h (Bset A N h)).card + h + 8 := by
      exact Erdos865.folded_additive h_ge_2 ( Erdos865.foldedOK_Bset hA hh h_ge_2 );
    have h_collisions_subset_Eset :
        (collisions h (Bset A N h)).card + #(Eset A N h \ collisions h (Bset A N h))
          = (Eset A N h).card := by
      rw [ ← Finset.card_union_of_disjoint ];
      · rw [ Finset.union_sdiff_of_subset ( collisions_subset_Eset hA hh ) ];
      · exact Finset.disjoint_sdiff;
    linarith [ card_XY_E A N h, Nat.sub_add_cancel ( by linarith : 1 ≤ h ) ];
  · interval_cases h <;> simp_all +decide [ Xset, Yset, Eset, Bset ]

end Erdos865
