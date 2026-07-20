/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Product and mixed intersection collections

This file constructs product intersection collections and mixed intersection
collections, proving the frequency and deficit bounds needed for Corollary 3.1.

**Reference**: Corollary 3.1 in Section 3 of the companion paper.
-/
import LeanPool.KaltonRoberts.Defs
import LeanPool.KaltonRoberts.Collections
import LeanPool.KaltonRoberts.Lemmas

/-!
# Product and mixed intersection collections

Product and mixed intersection collections with the frequency and deficit
bounds needed for the mixed-intersection step.
-/

namespace KaltonRoberts

open Finset BigOperators

variable {U : Type*} [DecidableEq U] [Fintype U]

/-! ## Helper: sum of products = (sum)^ℓ -/

private lemma sum_prod_eq_pow {J : Type*} [Fintype J]
    (w : J → ℝ) (ℓ : ℕ) :
    ∑ x : Fin ℓ → J, ∏ k : Fin ℓ, w (x k) = (∑ j : J, w j) ^ ℓ := by
  have h := @Finset.prod_univ_sum (Fin ℓ) ℝ _ _ (fun _ => J) _ (fun _ => Finset.univ) (fun _ j => w
    j)
  simp_all

/-! ## Two-set deficit intersection inequality -/

omit [Fintype U] in
/-- Deficit of an intersection is at most the sum of deficits plus 2. -/
theorem deficit_inter_le (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (M : ℝ) (hM : ∀ S : Finset U, |f S| ≤ M)
    (A B : Finset U) :
    deficit f M (A ∩ B) ≤ deficit f M A + deficit f M B + 2 := by
  unfold deficit;
  have h_mod : |f A + f B - f (A ∪ B) - f (A ∩ B)| ≤ 2 := by
    convert approx_modularity f hf A B using 1;
  grind

/-! ## Finite intersection deficit bound -/

/-- The intersection of a family indexed by `Fin ℓ`. -/
noncomputable def finsetInter (A : Fin ℓ → Finset U) : Finset U :=
  Finset.univ.inf A

/-- Deficit of ℓ-fold intersection is at most sum of deficits + 2*(ℓ-1). -/
theorem deficit_finsetInter_le (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (M : ℝ) (hM : ∀ S : Finset U, |f S| ≤ M)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (A : Fin ℓ → Finset U) :
    deficit f M (finsetInter A) ≤
      ∑ k : Fin ℓ, deficit f M (A k) + 2 * ((ℓ : ℝ) - 1) := by
  induction ℓ, hℓ using Nat.le_induction with
  | base =>
    simp +decide [finsetInter]
  | succ ℓ hℓ ih =>
    simp only [
      finsetInter,
      Fin.sum_univ_castSucc,
      Nat.cast_add,
      Nat.cast_one,
      add_sub_cancel_right]
    rw [
      show (Finset.univ.inf A : Finset U) =
          (Finset.univ.inf (fun k : Fin ℓ => A (Fin.castSucc k))) ∩ A (Fin.last ℓ) from
        ?_
      ];
    · have hih :
          deficit f M (Finset.univ.inf (fun k : Fin ℓ => A (Fin.castSucc k))) ≤
            (∑ k : Fin ℓ, deficit f M (A (Fin.castSucc k))) + 2 * ((ℓ : ℝ) - 1) := by
        simpa [finsetInter] using (ih fun k => A (Fin.castSucc k))
      linarith [
        deficit_inter_le f hf M hM
          (Finset.univ.inf fun k : Fin ℓ => A (Fin.castSucc k))
          (A (Fin.last ℓ)),
        hih]
    · ext x
      simp +decide only [Finset.mem_inf, Finset.mem_inter, Finset.mem_univ]
      exact ⟨fun h => ⟨fun i _ => h i.castSucc trivial, h (Fin.last ℓ) trivial⟩, fun h i _ => by
        cases i using Fin.lastCases <;> simp +decide [*]⟩

/-! ## Product intersection collection -/

/-- The ℓ-fold product intersection collection. -/
noncomputable def WeightedCollection.productInter
    (C : WeightedCollection U) (ℓ : ℕ) :
    WeightedCollection U where
  J := Fin ℓ → C.J
  sets := fun x => finsetInter (fun k => C.sets (x k))
  weight := fun x => ∏ k : Fin ℓ, C.weight (x k)
  weight_nonneg := fun x => Finset.prod_nonneg fun k _ => C.weight_nonneg (x k)
  total_pos := by
    rw [sum_prod_eq_pow]
    exact pow_pos C.totalWeight_pos ℓ

/-- Total weight of the product collection equals C.totalWeight^ℓ. -/
lemma WeightedCollection.productInter_totalWeight
    (C : WeightedCollection U) (ℓ : ℕ) :
    (C.productInter ℓ).totalWeight = C.totalWeight ^ ℓ := by
  exact sum_prod_eq_pow C.weight ℓ

/-- Item frequency of the product collection is at most (itemFreq C i)^ℓ. -/
lemma WeightedCollection.productInter_itemFreq
    (C : WeightedCollection U) (ℓ : ℕ) (i : U) :
    (C.productInter ℓ).itemFreq i ≤ (C.itemFreq i) ^ ℓ := by
  unfold WeightedCollection.itemFreq;
  rw [ div_pow, WeightedCollection.productInter_totalWeight ];
  rw [ ← sum_prod_eq_pow ];
  simp only [WeightedCollection.productInter, mul_ite, mul_one, mul_zero]
  gcongr;
  · exact pow_nonneg ( Finset.sum_nonneg fun _ _ => C.weight_nonneg _ ) _;
  · apply Finset.sum_le_sum
    intro x _
    by_cases hx : i ∈ finsetInter (fun k => C.sets (x k))
    · have hxk : ∀ k : Fin ℓ, i ∈ C.sets (x k) := by
        simpa [finsetInter, Finset.mem_inf] using hx
      simp [hx, hxk]
    · simp only [hx, if_false]
      exact Finset.prod_nonneg fun k _ => by
        by_cases hk : i ∈ C.sets (x k) <;> simp [hk, C.weight_nonneg]

/-- Average deficit of the product collection. -/
lemma WeightedCollection.productInter_avgDeficit
    (C : WeightedCollection U) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (M : ℝ) (hM : ∀ S : Finset U, |f S| ≤ M)
    (D : ℝ) (_hD : 0 ≤ D) (hdeficit : C.avgDeficit f M ≤ D) :
    (C.productInter ℓ).avgDeficit f M ≤
      ℓ * D + 2 * ((ℓ : ℝ) - 1) := by
  refine le_trans ?_ ( add_le_add ( mul_le_mul_of_nonneg_left hdeficit ( Nat.cast_nonneg _ ) )
    le_rfl );
  unfold WeightedCollection.avgDeficit
  norm_num [
    WeightedCollection.productInter_totalWeight,
    WeightedCollection.productInter]
  have h_prod :
      (∑ x : Fin ℓ → C.J,
        (∏ k, C.weight (x k)) * deficit f M (finsetInter (fun k => C.sets (x k)))) ≤
        (∑ x : Fin ℓ → C.J,
          (∏ k, C.weight (x k)) *
            (∑ k, deficit f M (C.sets (x k)) + 2 * (ℓ - 1))) :=
      by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left (deficit_finsetInter_le f hf M hM ℓ hℓ (fun k => C.sets (x
        k))) (Finset.prod_nonneg (fun k _ => C.weight_nonneg (x k)));
  have h_prod :
      (∑ x : Fin ℓ → C.J,
        (∏ k, C.weight (x k)) * (∑ k, deficit f M (C.sets (x k)))) =
        ℓ * C.totalWeight ^ (ℓ - 1) *
          (∑ j : C.J, C.weight j * deficit f M (C.sets j)) := by
    have h_prod : ∀ k : Fin ℓ,
        (∑ x : Fin ℓ → C.J,
          (∏ j, C.weight (x j)) * deficit f M (C.sets (x k))) =
          C.totalWeight ^ (ℓ - 1) *
            (∑ j : C.J, C.weight j * deficit f M (C.sets j)) := by
      intro k
      have h_prod :
          (∑ x : Fin ℓ → C.J,
            (∏ j, C.weight (x j)) * deficit f M (C.sets (x k))) =
            (∏ j : Fin ℓ,
              ∑ x : C.J, C.weight x *
                (if j = k then deficit f M (C.sets x) else 1)) := by
        simp +decide only [prod_sum];
        apply Finset.sum_bij (fun x _ => fun i _ => x i) <;>
          simp +decide only [univ_pi_univ, mem_univ, exists_const, forall_const, mul_ite,
            mul_one, prod_attach_univ]
        · simp_all
        · intro a₁ a₂ h
          exact funext fun i => congrFun (congrFun h i) (Finset.mem_univ i)
        · intro b
          exact ⟨fun i => b i (Finset.mem_univ i), funext fun i => funext fun _ => rfl⟩
        · intro x
          rw [← Finset.mul_prod_erase _ (fun j => C.weight (x j)) (Finset.mem_univ k)]
          rw [← Finset.mul_prod_erase _
            (fun j =>
              if j = k then C.weight (x j) * deficit f M (C.sets (x j)) else C.weight (x j))
            (Finset.mem_univ k)]
          have h_erase : (∏ j ∈ Finset.univ.erase k,
              if j = k then C.weight (x j) * deficit f M (C.sets (x j)) else C.weight (x j)) =
              ∏ j ∈ Finset.univ.erase k, C.weight (x j) := by
            apply Finset.prod_congr rfl
            simp_all
          rw [h_erase]
          simp +decide only [if_true]
          ring_nf
      simp_all only [mul_ite, mul_one, sum_ite_irrel]
      rw [← Finset.mul_prod_erase _
        (fun x : Fin ℓ =>
          if x = k then ∑ x : C.J, C.weight x * deficit f M (C.sets x) else ∑ x : C.J,
            C.weight x)
        (Finset.mem_univ k)]
      simp +decide only [if_true]
      have h_erase : (∏ x ∈ Finset.univ.erase k,
          if x = k then ∑ x : C.J, C.weight x * deficit f M (C.sets x) else ∑ x : C.J,
            C.weight x) =
          ∏ x ∈ Finset.univ.erase k, ∑ x : C.J, C.weight x := by
        apply Finset.prod_congr rfl
        simp_all
      rw [h_erase, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k),
        Finset.card_univ, Fintype.card_fin]
      rw [show C.totalWeight = ∑ x : C.J, C.weight x from rfl]
      ring_nf
    convert Finset.sum_congr rfl fun k ( hk : k ∈ Finset.univ ) => h_prod k using 1;
    · rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _ ];
    · simp +decide [ mul_assoc, Finset.mul_sum _ _ _ ];
  have h_prod :
      (∑ x : Fin ℓ → C.J, (∏ k, C.weight (x k)) * (2 * (ℓ - 1))) =
        2 * (ℓ - 1) * C.totalWeight ^ ℓ := by
    rw [ ← Finset.sum_mul _ _ _, sum_prod_eq_pow ]; ring_nf;
    rw [ show C.totalWeight = ∑ j : C.J, C.weight j from rfl ]; ring;
  have h_prod :
      (∑ x : Fin ℓ → C.J,
        (∏ k, C.weight (x k)) *
          (∑ k, deficit f M (C.sets (x k)) + 2 * (ℓ - 1))) =
        ℓ * C.totalWeight ^ (ℓ - 1) *
          (∑ j : C.J, C.weight j * deficit f M (C.sets j)) +
        2 * (ℓ - 1) * C.totalWeight ^ ℓ := by
    simp_all +decide [ mul_add, Finset.sum_add_distrib ];
  convert div_le_div_of_nonneg_right ( le_trans ‹_› h_prod.le ) ( pow_nonneg ( le_of_lt
    C.totalWeight_pos ) ℓ ) using 1;
  · unfold WeightedCollection.totalWeight WeightedCollection.productInter
    rw [sum_prod_eq_pow]
  · field_simp;
    rw [div_add', div_eq_div_iff] <;>
      norm_num [
        pow_succ,
        mul_assoc,
        mul_comm,
        mul_left_comm,
        ne_of_gt (show 0 < C.totalWeight from C.totalWeight_pos)]
    cases ℓ
    · simp_all
    · simp +decide [pow_succ']
      ring

/-! ## Mixed intersection collection

The key insight for the mixed collection: to make the convex combination
work with unnormalized collections, we multiply the ℓ-branch by TW^(ℓ+1)
and the (ℓ+1)-branch by TW^ℓ, equalizing the denominators.
The total weight becomes TW^(2ℓ+1).
-/

/-- The mixed intersection collection: weighted mixture of ℓ-fold and (ℓ+1)-fold
product intersections, with balanced weights so that frequency bounds work
correctly for unnormalized collections. -/
noncomputable def WeightedCollection.mixedInter
    (C : WeightedCollection U) (ℓ : ℕ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    WeightedCollection U where
  J := (Fin ℓ → C.J) ⊕ (Fin (ℓ + 1) → C.J)
  sets := fun j => match j with
    | Sum.inl x => finsetInter (fun k => C.sets (x k))
    | Sum.inr x => finsetInter (fun k => C.sets (x k))
  weight := fun j => match j with
    | Sum.inl x => (1 - τ) * C.totalWeight ^ (ℓ + 1) * (∏ k : Fin ℓ, C.weight (x k))
    | Sum.inr x => τ * C.totalWeight ^ ℓ * (∏ k : Fin (ℓ + 1), C.weight (x k))
  weight_nonneg := fun j => by
    cases j with
    | inl x =>
      apply mul_nonneg (mul_nonneg (by linarith) (pow_nonneg C.totalWeight_pos.le _))
      exact Finset.prod_nonneg fun k _ => C.weight_nonneg (x k)
    | inr x =>
      apply mul_nonneg (mul_nonneg hτ (pow_nonneg C.totalWeight_pos.le _))
      exact Finset.prod_nonneg fun k _ => C.weight_nonneg (x k)
  total_pos := by
    simp only [Fintype.sum_sum_type]
    rw [
      ← Finset.mul_sum,
      ← Finset.mul_sum,
      sum_prod_eq_pow C.weight ℓ,
      sum_prod_eq_pow C.weight (ℓ + 1)]
    have hpos : (0 : ℝ) < ∑ j : C.J, C.weight j := C.totalWeight_pos
    have h1 := pow_pos hpos ℓ
    have h2 := pow_pos hpos (ℓ + 1)
    have htw : C.totalWeight = ∑ j : C.J, C.weight j := rfl
    rw [htw]
    nlinarith [
      mul_nonneg (sub_nonneg.mpr hτ1) (mul_nonneg h2.le h1.le),
      mul_nonneg hτ (mul_nonneg h1.le h2.le)]

/-- Total weight of the mixed collection. -/
lemma WeightedCollection.mixedInter_totalWeight
    (C : WeightedCollection U) (ℓ : ℕ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (C.mixedInter ℓ τ hτ hτ1).totalWeight =
      C.totalWeight ^ (2 * ℓ + 1) := by
  unfold totalWeight mixedInter
  change
    (∑ x : (Fin ℓ → C.J) ⊕ (Fin (ℓ + 1) → C.J),
      match x with
      | Sum.inl x => (1 - τ) * C.totalWeight ^ (ℓ + 1) * ∏ k, C.weight (x k)
      | Sum.inr x => τ * C.totalWeight ^ ℓ * ∏ k, C.weight (x k)) =
        C.totalWeight ^ (2 * ℓ + 1)
  rw [Fintype.sum_sum_type]
  rw [
    ← Finset.mul_sum,
    ← Finset.mul_sum,
    sum_prod_eq_pow C.weight ℓ,
    sum_prod_eq_pow C.weight (ℓ + 1)]
  set S := ∑ j : C.J, C.weight j
  have htw : C.totalWeight = S := rfl
  rw [htw]
  ring

/-
Item frequency of the mixed collection.
-/
lemma WeightedCollection.mixedInter_itemFreq_le
    (C : WeightedCollection U) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (t : ℝ) (_ht : 0 ≤ t) (_ht1 : t ≤ 1)
    (hfreq : ∀ i : U, C.itemFreq i ≤ t) (i : U) :
    (C.mixedInter ℓ τ hτ hτ1).itemFreq i ≤
      (1 - τ) * t ^ ℓ + τ * t ^ (ℓ + 1) := by
  rw [ WeightedCollection.itemFreq ];
  rw [
    div_le_iff₀ (by
      exact (by
        exact
          WeightedCollection.mixedInter_totalWeight C ℓ τ hτ hτ1 ▸
            pow_pos C.totalWeight_pos _))
    ];
  have h_mixed_freq : (∑ x : Fin ℓ → C.J, (∏ k : Fin ℓ, C.weight (x k)) * (if i ∈ finsetInter (fun k
    => C.sets (x k)) then 1 else 0)) ≤ t ^ ℓ * (∑ j : C.J, C.weight j) ^ ℓ ∧ (∑ x : Fin (ℓ + 1) →
      C.J, (∏ k : Fin (ℓ + 1), C.weight (x k)) * (if i ∈ finsetInter (fun k => C.sets (x k)) then 1
        else 0)) ≤ t ^ (ℓ + 1) * (∑ j : C.J, C.weight j) ^ (ℓ + 1) := by
    have h_mixed_freq : ∀ k : ℕ, 1 ≤ k → (∑ x : Fin k → C.J, (∏ j : Fin k, C.weight (x j)) * (if i ∈
      finsetInter (fun j => C.sets (x j)) then 1 else 0)) ≤ t ^ k * (∑ j : C.J, C.weight j) ^ k :=
        by
      intro k hk
      have h_mixed_freq : (∑ x : Fin k → C.J, (∏ j : Fin k, C.weight (x j)) * (if i ∈ finsetInter
        (fun j => C.sets (x j)) then 1 else 0)) ≤ (∑ j : C.J, C.weight j * (if i ∈ C.sets j then 1
          else 0)) ^ k := by
        rw [ ← sum_prod_eq_pow ];
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : i ∈ finsetInter (fun j => C.sets (x j))
        · have hxj : ∀ j : Fin k, i ∈ C.sets (x j) := by
            simpa [finsetInter, Finset.mem_inf] using hx
          simp [hx, hxj]
        · simp only [hx, if_false]
          rw [mul_zero]
          apply Finset.prod_nonneg
          intro j _
          exact mul_nonneg (C.weight_nonneg (x j)) (by split_ifs <;> norm_num)
      have h_mixed_freq : (∑ j : C.J, C.weight j * (if i ∈ C.sets j then 1 else 0)) ≤ t * (∑ j :
        C.J, C.weight j) := by
        have := hfreq i;
        rwa [ WeightedCollection.itemFreq, div_le_iff₀ ( C.totalWeight_pos ) ] at this;
      exact le_trans ‹_› ( by rw [ ← mul_pow ]; exact pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _
        => mul_nonneg ( C.weight_nonneg _ ) ( by split_ifs <;> norm_num ) ) h_mixed_freq _ );
    exact ⟨ h_mixed_freq ℓ hℓ, h_mixed_freq ( ℓ + 1 ) ( Nat.le_succ_of_le hℓ ) ⟩;
  convert add_le_add ( mul_le_mul_of_nonneg_left h_mixed_freq.1 ( show 0 ≤ ( 1 - τ ) * ( ∑ j : C.J,
    C.weight j ) ^ ( ℓ + 1 ) by exact mul_nonneg ( sub_nonneg.2 hτ1 ) ( pow_nonneg (
      Finset.sum_nonneg fun _ _ => C.weight_nonneg _ ) _ ) ) ) ( mul_le_mul_of_nonneg_left
        h_mixed_freq.2 ( show 0 ≤ τ * ( ∑ j : C.J, C.weight j ) ^ ℓ by exact mul_nonneg hτ (
          pow_nonneg ( Finset.sum_nonneg fun _ _ => C.weight_nonneg _ ) _ ) ) ) using 1;
  · change
      (∑ x : (Fin ℓ → C.J) ⊕ (Fin (ℓ + 1) → C.J),
        (match x with
        | Sum.inl x => (1 - τ) * C.totalWeight ^ (ℓ + 1) * ∏ k, C.weight (x k)
        | Sum.inr x => τ * C.totalWeight ^ ℓ * ∏ k, C.weight (x k)) *
          if i ∈ match x with
          | Sum.inl x => finsetInter (fun k => C.sets (x k))
          | Sum.inr x => finsetInter (fun k => C.sets (x k)) then 1 else 0)
        =
      (1 - τ) * (∑ j : C.J, C.weight j) ^ (ℓ + 1) *
          (∑ x : Fin ℓ → C.J, (∏ k, C.weight (x k)) *
            if i ∈ finsetInter (fun k => C.sets (x k)) then 1 else 0) +
        τ * (∑ j : C.J, C.weight j) ^ ℓ *
          (∑ x : Fin (ℓ + 1) → C.J, (∏ k, C.weight (x k)) *
            if i ∈ finsetInter (fun k => C.sets (x k)) then 1 else 0)
    rw [Fintype.sum_sum_type]
    simp [
      WeightedCollection.totalWeight,
      mul_ite,
      Finset.mul_sum,
      mul_assoc,
      mul_comm,
      mul_left_comm]
  · rw [WeightedCollection.mixedInter_totalWeight]
    rw [show C.totalWeight = ∑ j : C.J, C.weight j from rfl]
    ring

/-
Average deficit of the mixed collection.
-/
lemma WeightedCollection.mixedInter_avgDeficit_le
    (C : WeightedCollection U) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (M : ℝ) (hM : ∀ S : Finset U, |f S| ≤ M)
    (D : ℝ) (hD : 0 ≤ D) (hdeficit : C.avgDeficit f M ≤ D) :
    (C.mixedInter ℓ τ hτ hτ1).avgDeficit f M ≤
      ℓ * D + 2 * ((ℓ : ℝ) - 1) + τ * (D + 2) := by
  unfold WeightedCollection.avgDeficit WeightedCollection.mixedInter;
  rw [ Fintype.sum_sum_type, div_le_iff₀ ];
  · have h_left : (∑ x : Fin ℓ → C.J, (∏ k : Fin ℓ, C.weight (x k)) * deficit f M (finsetInter (fun
    k => C.sets (x k)))) ≤ C.totalWeight ^ ℓ * (ℓ * D + 2 * (ℓ - 1)) := by
      have h := WeightedCollection.productInter_avgDeficit C ℓ hℓ f hf M hM D hD hdeficit
      rw [WeightedCollection.avgDeficit, WeightedCollection.productInter_totalWeight] at h
      rw [div_le_iff₀ (pow_pos C.totalWeight_pos ℓ)] at h
      exact h.trans_eq (by ring)
    have h_right : (∑ x : Fin (ℓ + 1) → C.J, (∏ k : Fin (ℓ + 1), C.weight (x k)) * deficit f M
      (finsetInter (fun k => C.sets (x k)))) ≤ C.totalWeight ^ (ℓ + 1) * ((ℓ + 1) * D + 2 * ℓ) := by
      have h := WeightedCollection.productInter_avgDeficit C (ℓ + 1) (Nat.le_succ_of_le hℓ) f hf M
        hM D hD hdeficit
      rw [WeightedCollection.avgDeficit, WeightedCollection.productInter_totalWeight] at h
      rw [div_le_iff₀ (pow_pos C.totalWeight_pos (ℓ + 1))] at h
      exact h.trans_eq (by norm_num [Nat.cast_add, Nat.cast_one]; ring)
    convert add_le_add ( mul_le_mul_of_nonneg_left h_left ( show 0 ≤ ( 1 - τ ) * C.totalWeight ^ ( ℓ
      + 1 ) by exact mul_nonneg ( sub_nonneg.2 hτ1 ) ( pow_nonneg C.totalWeight_pos.le _ ) ) ) (
        mul_le_mul_of_nonneg_left h_right ( show 0 ≤ τ * C.totalWeight ^ ℓ by exact mul_nonneg hτ (
          pow_nonneg C.totalWeight_pos.le _ ) ) ) using 1;
    · simp +decide only [mul_assoc, Finset.mul_sum _ _ _];
    · erw [WeightedCollection.mixedInter_totalWeight C ℓ τ hτ hτ1]
      ring
  · apply_rules [ mul_pos, pow_pos, WeightedCollection.totalWeight_pos ]

end KaltonRoberts
